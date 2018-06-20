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
        return app && r.get_head() && r.get_head()->get_decl() == app->get_decl();
    }

    bool mk_synchronize::exists_recursive(app * app, rule_set & rules) const {
        func_decl* app_decl = app->get_decl();
        rule_vector const & src_rules = rules.get_predicate_rules(app_decl);
        for (rule_vector::const_iterator it = src_rules.begin(); it != src_rules.end(); ++it) {
            rule *r = *it;
            unsigned positive_tail_size = r->get_positive_tail_size();
            for (unsigned i = 0; i < positive_tail_size; ++i) {
                if (r->get_decl(i) == app_decl) {
                    return true;
                }
            }
        }
        return false;
    }

    void mk_synchronize::replace_applications(rule & r, rule_set & rules, ptr_vector<app> & apps, func_decl * pred) {
        app* replacing = product_application(apps, pred);

        ptr_vector<app> new_tail;
        svector<bool> new_tail_neg;
        unsigned n = r.get_tail_size() - apps.size() + 1;
        unsigned tail_idx = 0;
        new_tail.resize(n);
        new_tail_neg.resize(n);
        new_tail[0] = replacing;
        new_tail_neg[0] = false;

        // TODO: unify with product_application
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

    vector<rule_vector> mk_synchronize::rename_bound_vars(ptr_vector<func_decl> const & heads, rule_set & rules) {
        vector<rule_vector> result;
        result.resize(heads.size());
        unsigned var_idx = 0;
        for (unsigned i = 0; i < heads.size(); ++i) {
            func_decl * head = heads[i];
            rule_vector const & src_rules = rules.get_predicate_rules(head);
            rule_vector dst_vector;
            dst_vector.resize(src_rules.size());
            for (unsigned j = 0; j < src_rules.size(); ++j) {
                rule * new_rule = rename_bound_vars_in_rule(src_rules[j], var_idx);
                dst_vector[j] = new_rule;
            }
            result[i] = dst_vector;
        }
        return result;
    }

    app* mk_synchronize::product_application(ptr_vector<app> const &apps, func_decl * pred) {
        ptr_vector<app>::const_iterator it = apps.begin(), end = apps.end();
        unsigned args_num = 0;
        for (; it != end; ++it) {
            args_num += (*it)->get_num_args();
        }
        ptr_vector<expr> args;
        args.resize(args_num);
        it = apps.begin();
        for (unsigned args_idx = 0; it != end; ++it) {
            app* a = *it;
            for (unsigned i = 0; i < a->get_num_args(); ++i, ++args_idx) {
                args[args_idx] = a->get_arg(i);
                // std::cout << " " << a->get_arg(i);
            }
            // std::cout << std::endl;
        }

        return m.mk_app(pred, args_num, args.c_ptr());
    }

    rule_ref mk_synchronize::product_rule(rule_vector const & rules, func_decl * pred) {
        // printf("Computing product of %d rules...\n", rules.size());
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
        for (unsigned i = 0; i < rules.size(); ++i) {
            heads[i] = rules[i]->get_head();
        }
        app* product_head = product_application(heads, pred);
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
                new_tail[tail_idx] = product_application(merged_recursive_calls, pred);
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

    void mk_synchronize::merge_rules(unsigned idx, ptr_vector<func_decl> const & decls, rule_vector &buf,
            vector<rule_vector> const & merged_rules, rule_set & all_rules, func_decl * pred) {
        //std::cout << "merge_rules, idx: " << idx << "; count: " << decls.size() << std::endl;
        if (idx >= decls.size()) {
            rule_ref product = product_rule(buf, pred);
            //std::cout << "ADDING RULE " << std::endl;
            //product->display(m_ctx, std::cout);
            all_rules.add_rule(product.get());
            return;
        }

        rule_vector const & pred_rules = merged_rules[idx];
        for (rule_vector::const_iterator it = pred_rules.begin(); it != pred_rules.end(); ++it) {
            buf[idx] = *it;
            merge_rules(idx + 1, decls, buf, merged_rules, all_rules, pred);
        }
    }

    void mk_synchronize::merge_applications(rule & r, rule_set & rules) {
        // printf("ATTENTION: trying to merge applications in\n");
        // r.display(rules.get_context(), std::cout);
        ptr_vector<app> non_recursive_applications;
        for (unsigned i = 0; i < r.get_positive_tail_size(); ++i) {
            app* application = r.get_tail(i);
            if (!is_recursive_app(r, application) && exists_recursive(application, rules)) {
                non_recursive_applications.push_back(application);
            }
        }
        if (non_recursive_applications.size() < 2) {
            // printf("Skipping rule: too few non-recursive relations (%d)\n", non_recursive_applications.size());
            return;
        }

        // printf("Merging %d applications...\n", non_recursive_applications.size());
        string_buffer<> buffer;
        ptr_vector<sort> domain;

        std::sort(non_recursive_applications.begin(), non_recursive_applications.end(), app_compare());

        ptr_vector<app>::const_iterator it = non_recursive_applications.begin(), end = non_recursive_applications.end();
        for (; it != end; ++it) {
            func_decl* decl = (*it)->get_decl();
            buffer << decl->get_name();
            buffer << "!!";
            domain.append(decl->get_arity(), decl->get_domain());
        }

        symbol new_name = symbol(buffer.c_str());
        func_decl* product_pred;


        if (!cache.contains(new_name)) {
            // TODO: do not forget to check rules.contains(func_decl)
            func_decl* orig = non_recursive_applications[0]->get_decl();
            product_pred = m_ctx.mk_fresh_head_predicate(new_name,
                symbol::null, domain.size(), domain.c_ptr(), orig);
            // std::cout << "Created fresh relation symbol " << product_pred->get_name() << std::endl;

            cache.insert(new_name, product_pred);

            ptr_vector<func_decl> merged_decls;
            rule_vector rules_buf;
            unsigned n = non_recursive_applications.size();
            merged_decls.resize(n);
            rules_buf.resize(n);
            for (unsigned i = 0; i < n; ++i) {
                merged_decls[i] = non_recursive_applications[i]->get_decl();
            }

            vector<rule_vector> renamed_rules = rename_bound_vars(merged_decls, rules);
            merge_rules(0, merged_decls, rules_buf, renamed_rules, rules, product_pred);
        }

        else {
            product_pred = cache[new_name];
        }
        replace_applications(r, rules, non_recursive_applications, product_pred);
    }

    rule_set * mk_synchronize::operator()(rule_set const & source) {
        // printf("\n\n----------------------------------\nSYNCHRONIZING! SOURCE RULES:\n");
        // source.display(std::cout);

        rule_set* rules = alloc(rule_set, m_ctx);
        rules->inherit_predicates(source);

        rule_set::iterator it = source.begin(), end = source.end();
        for (; it != end; ++it) {
            rules->add_rule(*it);
        }

        unsigned current_rule = 0;
        while (current_rule < rules->get_num_rules()) {
            rule *r = rules->get_rule(current_rule);
            merge_applications(*r, *rules);
            ++current_rule;
        }

        // printf("\n\n-----------------RESULTING RULES:-----------------\n");
        // rules->display(std::cout);
        // printf("\n\n----------------------------------\n");
        return rules;
    }

};
