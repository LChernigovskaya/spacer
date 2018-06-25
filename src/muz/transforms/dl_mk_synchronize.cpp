/*++
Copyright (c) 2017 Saint-Petersburg State University

Module Name:

    dl_mk_synchronize.h

Abstract:

    Rule transformer that attempts to merge recursive iterations
    relaxing the shape of the inductive invariant.

Author:

    Dmitry Mordvinov (dvvrd) 2017-05-24

Revision History:

--*/
#include "dl_mk_synchronize.h"

namespace datalog {

    mk_synchronize::mk_synchronize(context& ctx, unsigned priority):
        rule_transformer::plugin(priority, false),
        m_ctx(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager())
    {}

    bool mk_synchronize::is_recursive_app(rule & r, app * app) const {
        func_decl* head_decl = r.get_head()->get_decl();
        func_decl* app_decl = app->get_decl();
        if (head_decl == app_decl) {
            return true;
        }
        rule_stratifier::comp_vector const & strata = m_stratifier->get_strats();
        for (unsigned i = 0; i < strata.size(); ++i) {
            if (strata[i]->contains(head_decl)) {
                return (strata[i]->contains(app_decl));
            }
        }
        return false;
    }

    bool mk_synchronize::exists_recursive(app * app) const {
        func_decl* app_decl = app->get_decl();
        if (m_deps->get_deps(app_decl).contains(app_decl)) {
            return true;
        }
        rule_stratifier::comp_vector const & strata = m_stratifier->get_strats();
        for (unsigned i = 0; i < strata.size(); ++i) {
            if (strata[i]->contains(app_decl)) {
                return (strata[i]->size() > 1);
            }
        }
        return false;
    }

    ptr_vector<rule_stratifier::item_set> mk_synchronize::add_merged_decls(ptr_vector<app> apps) {
        unsigned n = apps.size();
        ptr_vector<rule_stratifier::item_set> merged_decls;
        merged_decls.resize(n);
        ptr_vector<func_decl> app_decls;
        app_decls.resize(n);
        for(unsigned j = 0; j < n; ++j) {
            app_decls[j] = apps[j]->get_decl();
        }
        rule_stratifier::comp_vector const & strata = m_stratifier->get_strats();
        for (unsigned i = 0; i < strata.size(); ++i) {
            for (unsigned j = 0; j < n; ++j) {
                if (strata[i]->contains(app_decls[j])) {
                    merged_decls[j] = strata[i];
                }
            }
        }
        return merged_decls;
    }

    void mk_synchronize::add_new_rel_symbols(unsigned idx, ptr_vector<rule_stratifier::item_set> const & decls,
            ptr_vector<func_decl> & decls_buf, bool & was_added) {
        if (idx >= decls.size()) {
            string_buffer<> buffer;
            ptr_vector<sort> domain;
            ptr_vector<func_decl>::const_iterator it = decls_buf.begin(), end = decls_buf.end();
            for (; it != end; ++it) {
                buffer << (*it)->get_name();
                buffer << "!!";
                domain.append((*it)->get_arity(), (*it)->get_domain());
            }

            symbol new_name = symbol(buffer.c_str());

            if (!cache.contains(new_name)) {
                was_added = true;
                func_decl* orig = decls_buf[0];
                func_decl* product_pred = m_ctx.mk_fresh_head_predicate(new_name,
                    symbol::null, domain.size(), domain.c_ptr(), orig);
                cache.insert(new_name, product_pred);
            }
            return;
        }

        rule_stratifier::item_set const & pred_decls = (*decls[idx]);
        for (rule_stratifier::item_set::iterator it = pred_decls.begin(); it != pred_decls.end(); ++it) {
            buf[idx] = *it;
            add_new_rel_symbols(idx + 1, decls, decls_buf, was_added);
        }
    }

    void mk_synchronize::replace_applications(rule & r, rule_set & rules, ptr_vector<app> & apps) {
        app* replacing = product_application(apps);

        ptr_vector<app> new_tail;
        svector<bool> new_tail_neg;
        unsigned n = r.get_tail_size() - apps.size() + 1;
        unsigned tail_idx = 0;
        new_tail.resize(n);
        new_tail_neg.resize(n);
        new_tail[0] = replacing;
        new_tail_neg[0] = false;

        for (unsigned i = 0; i < r.get_positive_tail_size(); ++i) {
            app* tail = r.get_tail(i);
            if (!apps.contains(tail)) {
                ++tail_idx;
                new_tail[tail_idx] = tail;
                new_tail_neg[tail_idx] = false;
            }
        }
        for (unsigned i = r.get_positive_tail_size(); i < r.get_uninterpreted_tail_size(); ++i) {
            ++tail_idx;
            new_tail[tail_idx] = r.get_tail(i);
            new_tail_neg[tail_idx] = true;
        }
        for (unsigned i = r.get_uninterpreted_tail_size(); i < r.get_tail_size(); ++i) {
            ++tail_idx;
            new_tail[tail_idx] = r.get_tail(i);
            new_tail_neg[tail_idx] = false;
        }

        rule_ref new_rule(rm);
        new_rule = rm.mk(r.get_head(), tail_idx + 1,
            new_tail.c_ptr(), new_tail_neg.c_ptr(), symbol::null, false);
        rules.replace_rule(&r, new_rule.get());
    }

    rule * mk_synchronize::rename_bound_vars_in_rule(rule * r, unsigned & var_idx) {
        ptr_vector<sort> sorts;
        r->get_vars(m, sorts);
        expr_ref_vector revsub(m);
        revsub.resize(sorts.size());
        for (unsigned i = 0; i < sorts.size(); ++i) {
            if (sorts[i]) {
                revsub[i] = m.mk_var(var_idx++, sorts[i]);
            }
        }

        rule_ref new_rule(rm);
        new_rule = rm.mk(r);
        rm.substitute(new_rule, revsub.size(), revsub.c_ptr());

        return new_rule.steal();
    }

    vector<rule_vector> mk_synchronize::rename_bound_vars(ptr_vector<rule_stratifier::item_set> const & heads, rule_set & rules) {
        vector<rule_vector> result;
        result.resize(heads.size());
        unsigned var_idx = 0;
        for (unsigned i = 0; i < heads.size(); ++i) {
            rule_vector dst_vector;
            for (rule_stratifier::item_set::iterator it = heads[i]->begin(); it != heads[i]->end(); ++it) {
                func_decl * head = *it;
                rule_vector const & src_rules = rules.get_predicate_rules(head);
                for (unsigned j = 0; j < src_rules.size(); ++j) {
                    rule * new_rule = rename_bound_vars_in_rule(src_rules[j], var_idx);
                    dst_vector.insert(new_rule);
                }
            }
            result[i] = dst_vector;
        }
        return result;
    }

    app* mk_synchronize::product_application(ptr_vector<app> const &apps) {
        ptr_vector<app>::const_iterator it = apps.begin(), end = apps.end();
        unsigned args_num = 0;
        string_buffer<> buffer;

        for (; it != end; ++it) {
            buffer << (*it)->get_decl()->get_name();
            buffer << "!!";
            args_num += (*it)->get_num_args();
        }

        symbol name = symbol(buffer.c_str());
        SASSERT(cache.contains(name));
        func_decl * pred = cache[name];

        ptr_vector<expr> args;
        args.resize(args_num);
        it = apps.begin();
        for (unsigned args_idx = 0; it != end; ++it) {
            app* a = *it;
            for (unsigned i = 0; i < a->get_num_args(); ++i, ++args_idx) {
                args[args_idx] = a->get_arg(i);
            }
        }

        return m.mk_app(pred, args_num, args.c_ptr());
    }

    rule_ref mk_synchronize::product_rule(rule_vector const & rules) {
        unsigned n = rules.size();

        string_buffer<> buffer;
        bool first_rule = true;
        for (rule_vector::const_iterator it = rules.begin(); it != rules.end(); ++it, first_rule = false) {
            if (!first_rule) {
                buffer << "+";
            }
            buffer << (*it)->name();
        }

        ptr_vector<app> heads;
        heads.resize(n);
        for (unsigned i = 0; i < n; ++i) {
            heads[i] = rules[i]->get_head();
        }
        app* product_head = product_application(heads);
        unsigned product_tail_length = 0;
        bool has_recursion = false;
        vector< ptr_vector<app> > recursive_calls;
        recursive_calls.resize(n);
        for (unsigned i = 0; i < n; ++i) {
            rule& rule = *rules[i];
            product_tail_length += rule.get_tail_size();
            for (unsigned j = 0; j < rule.get_positive_tail_size(); ++j) {
                app* tail = rule.get_tail(j);
                if (is_recursive_app(rule, tail)) {
                    has_recursion = true;
                    recursive_calls[i].push_back(tail);
                }
            }
            if (recursive_calls[i].empty()) {
                recursive_calls[i].push_back(rule.get_head());
            }
        }

        ptr_vector<app> new_tail;
        svector<bool> new_tail_neg;
        new_tail.resize(product_tail_length);
        new_tail_neg.resize(product_tail_length);
        unsigned tail_idx = -1;
        if (has_recursion) {
            int max_size = recursive_calls[0].size();
            for (unsigned i = 0; i < n; ++i) {
                if (recursive_calls[i].size() > max_size) {
                    max_size = recursive_calls[i].size();
                }
            }
            for (unsigned j = 0; j < max_size; ++j) {
                ptr_vector<app> merged_recursive_calls;
                merged_recursive_calls.resize(n);
                for (unsigned i = 0; i < n; ++i) {
                    unsigned cur_size = recursive_calls[i].size();
                    if (j < cur_size) {
                        merged_recursive_calls[i] = recursive_calls[i][j];
                    }
                    else {
                        merged_recursive_calls[i] = recursive_calls[i][cur_size - 1];
                    }
                }
                ++tail_idx;
                new_tail[tail_idx] = product_application(merged_recursive_calls);
                new_tail_neg[tail_idx] = false;
            }
        }

        for (rule_vector::const_iterator it = rules.begin(); it != rules.end(); ++it) {
            rule& rule = **it;
            for (unsigned i = 0; i < rule.get_positive_tail_size(); ++i) {
                app* tail = rule.get_tail(i);
                if (!is_recursive_app(rule, tail)) {
                    ++tail_idx;
                    new_tail[tail_idx] = tail;
                    new_tail_neg[tail_idx] = false;
                }
            }
            for (unsigned i = rule.get_positive_tail_size(); i < rule.get_uninterpreted_tail_size(); ++i) {
                ++tail_idx;
                new_tail[tail_idx] = rule.get_tail(i);
                new_tail_neg[tail_idx] = true;
            }
            for (unsigned i = rule.get_uninterpreted_tail_size(); i < rule.get_tail_size(); ++i) {
                ++tail_idx;
                new_tail[tail_idx] = rule.get_tail(i);
                new_tail_neg[tail_idx] = rule.is_neg_tail(i);
            }
        }

        rule_ref new_rule(rm);
        new_rule = rm.mk(product_head, tail_idx + 1,
            new_tail.c_ptr(), new_tail_neg.c_ptr(), symbol(buffer.c_str()), false);
        rm.fix_unbound_vars(new_rule, false);
        return new_rule;
    }

    void mk_synchronize::merge_rules(unsigned idx, rule_vector & buf, vector<rule_vector> const & merged_rules,
            rule_set & all_rules) {
        if (idx >= merged_rules.size()) {
            rule_ref product = product_rule(buf);
            all_rules.add_rule(product.get());
            return;
        }

        rule_vector const & pred_rules = merged_rules[idx];
        for (rule_vector::const_iterator it = pred_rules.begin(); it != pred_rules.end(); ++it) {
            buf[idx] = *it;
            merge_rules(idx + 1, buf, merged_rules, all_rules);
        }
    }

    void mk_synchronize::merge_applications(rule & r, rule_set & rules) {
        ptr_vector<app> non_recursive_applications;
        for (unsigned i = 0; i < r.get_positive_tail_size(); ++i) {
            app* application = r.get_tail(i);
            if (!is_recursive_app(r, application) && exists_recursive(application)) {
                non_recursive_applications.push_back(application);
            }
        }
        if (non_recursive_applications.size() < 2) {
            return;
        }
        std::sort(non_recursive_applications.begin(), non_recursive_applications.end(), app_compare());

        ptr_vector<rule_stratifier::item_set> merged_decls = add_merged_decls(non_recursive_applications);

        unsigned n = non_recursive_applications.size();
        ptr_vector<func_decl> decls_buf;
        decls_buf.resize(n);
        bool was_added = false;
        add_new_rel_symbols(0, merged_decls, decls_buf, was_added);
        if (was_added){
            rule_vector rules_buf;
            rules_buf.resize(n);
            vector<rule_vector> renamed_rules = rename_bound_vars(merged_decls, rules);
            merge_rules(0, rules_buf, renamed_rules, rules);
        }

        replace_applications(r, rules, non_recursive_applications);
        m_deps->populate(rules);
        m_stratifier = alloc(rule_stratifier, *m_deps);
    }

    rule_set * mk_synchronize::operator()(rule_set const & source) {
        rule_set* rules = alloc(rule_set, m_ctx);
        rules->inherit_predicates(source);

        rule_set::iterator it = source.begin(), end = source.end();
        for (; it != end; ++it) {
            rules->add_rule(*it);
        }

        m_deps = alloc(rule_dependencies, m_ctx);
        m_deps->populate(*rules);
        m_stratifier = alloc(rule_stratifier, *m_deps);

        unsigned current_rule = 0;
        while (current_rule < rules->get_num_rules()) {
            rule *r = rules->get_rule(current_rule);
            merge_applications(*r, *rules);
            ++current_rule;
        }
        return rules;
    }

};
