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
#include "ast_util.h"
#include "expr_safe_replace.h"
#include"fixedpoint_params.hpp"
#include "dl_mk_unfold.h"

namespace datalog {

    // -----------------------------------
    //
    // utils
    //
    // -----------------------------------

    struct scoped_push {
    private:
        smt::kernel & m_solver;
    public:
        scoped_push(smt::kernel & solver) : m_solver(solver) {
            m_solver.push();
        }
        ~scoped_push() {
            m_solver.pop(1);
        }
    };

    symbol concat(char const * s, unsigned n) {
        std::stringstream ss;
        ss << s << n;
        return symbol(ss.str().c_str());
    }

    // expr * fresh_const(ast_manager & m, char const *prefix, unsigned idx, sort * s) {
    //     return m.mk_const(concat(prefix, idx), s);
    // }

    vector<ptr_vector<expr> > replace_bound_vars(ast_manager & m, bool with_consts, unsigned & delta,
            vector<ptr_vector<expr> > const & exprs, ptr_vector<sort> & var_sorts, svector<symbol> & var_names) {
        used_vars used;
        for (vector<ptr_vector<expr> >::const_iterator it1 = exprs.begin(); it1 != exprs.end(); ++it1) {
            ptr_vector<expr> const & v = *it1;
            for (ptr_vector<expr>::const_iterator it2 = v.begin(); it2 != v.end(); ++it2) {
                used.process(*it2);
            }
        }

        ptr_vector<sort> sorts;
        unsigned sz = used.get_max_found_var_idx_plus_1();
        for (unsigned i = 0; i < sz; ++i) {
            sort* s = used.get(i);
            sorts.push_back(s ? s : m.mk_bool_sort());
        }

        expr_ref_vector revsub(m);
        revsub.resize(sorts.size());
        for (unsigned i = 0; i < sorts.size(); ++i) {
            expr * bv = with_consts ? static_cast<expr*>(m.mk_fresh_const("__cv", sorts[i])) : m.mk_var(delta, sorts[i]);
            revsub[i] = bv;
            var_sorts.push_back(sorts[i]);
            var_names.push_back(with_consts ? to_app(bv)->get_decl()->get_name() : concat("__bv", delta));
            ++delta;
        }

        expr_ref tmp(m);
        var_subst vs(m, false);
        vector<ptr_vector<expr> > result;
        result.resize(exprs.size());
        for (unsigned i = 0; i < exprs.size(); ++i) {
            ptr_vector<expr> const & v = exprs[i];
            result[i].resize(exprs[i].size());
            for (unsigned j = 0; j < exprs[i].size(); ++j) {
                vs(exprs[i][j], revsub.size(), revsub.c_ptr(), tmp);
                result[i][j] = tmp.steal();
            }
        }
        return result;
    }

    ptr_vector<expr> replace_vars_with_consts(ast_manager & m, unsigned & delta, unsigned num_exprs, expr * const* exprs) {
        vector<ptr_vector<expr> > input;
        ptr_vector<sort> tmp1;
        svector<symbol> tmp2;
        input.push_back(ptr_vector<expr>(num_exprs, exprs));
        return replace_bound_vars(m, true, delta, input, tmp1, tmp2)[0];
    }

    // -----------------------------------
    //
    // rules reachability
    //
    // -----------------------------------

    rule_reachability_graph::rule_reachability_graph(context & ctx, rule_set const & rules)
          : rule_dependencies_base(ctx),
            m_rules(rules),
            m_unify(ctx),
            m(ctx.get_manager()),
            m_solver(m, m_smt_params) {
        populate(rules);
    }

    rule_reachability_graph::~rule_reachability_graph() {
    }

    bool rule_reachability_graph::check_reachability(rule & src, unsigned tail_idx, rule & dst, rule_ref & tmp) {
        if (m_unify.unify_rules(src, tail_idx, dst)) {
            if (m_unify.apply(src, tail_idx, dst, tmp)) {
                rule * r = tmp.get();
                m_solver.reset();
                ptr_vector<expr> interpreted_tail;
                for (unsigned i = r->get_uninterpreted_tail_size(); i < r->get_tail_size(); ++i) {
                    interpreted_tail.push_back(r->get_tail(i));
                }
                unsigned delta = 0;
                ptr_vector<expr> exprs = replace_vars_with_consts(m, delta, interpreted_tail.size(), interpreted_tail.c_ptr());
                for (unsigned i = 0; i < exprs.size(); ++i) {
                    m_solver.assert_expr(exprs[i]);
                }
                lbool is_sat = m_solver.check();
                // std::cout << "got " << is_sat << std::endl;
                return is_sat == l_true;
            }
            return false;
        }
        return false;
        // return m_unify.unify_rules(src, tail_idx, dst) && m_unify.apply(src, tail_idx, dst, tmp);
        // if (m_unify.unify_rules(src, tail_idx, dst) &&
        //     m_unify.apply(src, tail_idx, dst, tmp)) {
        //     expr_ref_vector s1 = m_unify.get_rule_subst(src, true);
        //     expr_ref_vector s2 = m_unify.get_rule_subst(dst, false);
        //     resolve_rule(m_rules.get_rule_manager(), src, dst, tail_idx, s1, s2, *tmp.get());
        //     return true;
        // }

        // return false;
    }

    void rule_reachability_graph::populate_one(rule * r) {
        TRACE("dl_verbose", tout << r->get_decl()->get_name() << "\n";);
        m_visited.reset();
        item_set & s = ensure_key(r);
        s.insert(r);

        rule_ref tmp_rule(m_rules.get_rule_manager());
        for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
            const rule_vector &potential_deps = m_rules.get_predicate_rules(r->get_tail(i)->get_decl());
            rule_vector::const_iterator it = potential_deps.begin(), end = potential_deps.end();
            for (; it != end; ++it) {
                rule * dst = *it;
                if (!s.contains(dst) && check_reachability(*r, i, *dst, tmp_rule)) {
                    s.insert(dst);
                    ensure_key(dst);
                }
            }
        }
    }

    void rule_reachability_graph::connect(rule * r1, rule * r2) {
        item_set & s = ensure_key(r1);
        if (!s.contains(r2)) {
            s.insert(r2);
            ensure_key(r2);
        }
    }

    void rule_reachability_graph::display( std::ostream & out ) const {
        iterator pit = begin();
        iterator pend = end();
        for (; pit != pend; ++pit) {
            rule * r = pit->m_key;
            const item_set & deps = *pit->m_value;
            item_set::iterator dit = deps.begin();
            item_set::iterator dend = deps.end();
            if (dit == dend) {
                out << r->name() << " - <none>\n";
            }
            for (; dit != dend; ++dit) {
                rule * dep = *dit;
                out << r->name() << " -> " << dep->name() << "\n";
            }
        }
    }

    reachability_stratifier::reachability_stratifier(rule_reachability_graph const & graph)
          : rule_stratifier_base(graph),
            m_graph(graph) {
    }

    reachability_stratifier::~reachability_stratifier() {
    }

    bool reachability_stratifier::validate_mutual_recursion() const {
        for (unsigned i = 0; i < m_strats.size(); ++i) {
            item_set::iterator it  = m_strats[i]->begin();
            item_set::iterator end = m_strats[i]->end();
            func_decl * head;
            if (it != end) {
                head = (*it)->get_head()->get_decl();
            }
            for (; it != end; ++it) {
                if ((*it)->get_head()->get_decl() != head) {
                    IF_VERBOSE (1, verbose_stream () << "Synchronization of mutual recursion is currently not supported";);
                    return false;
                }
            }
        }
        return true;
    }

    void reachability_stratifier::display( std::ostream & out ) const {
        m_graph.display(out << "dependencies\n");
        out << "strata\n";
        for (unsigned i = 0; i < m_strats.size(); ++i) {
            item_set::iterator it  = m_strats[i]->begin();
            item_set::iterator end = m_strats[i]->end();
            for (; it != end; ++it) {
                out << (*it)->name() << " ";
            }
            out << "\n";
        }
    }

    bool reachability_stratifier::strata_connected(item_set & src, item_set & dst) const {
        for (item_set::iterator it1 = src.begin(); it1 != src.end(); ++it1) {
            for (item_set::iterator it2 = dst.begin(); it2 != dst.end(); ++it2) {
                if (m_graph.get_deps(*it1).contains(*it2)) {
                    return true;
                }
            }
        }
        return false;
    }

    bool reachability_stratifier::is_non_recursive_stratum(item_set & s) const {
        if (s.size() != 1) {
            return false;
        }
        rule & r = **s.begin();
        func_decl * f = r.get_head()->get_decl();
        for (unsigned i = 0; i < r.get_uninterpreted_tail_size(); ++i) {
            if (r.get_tail(i)->get_decl() == f) {
                return false;
            }
        }
        return true;
    }

    // -----------------------------------
    //
    // synchronization lemma
    //
    // -----------------------------------

    lemma::lemma(ast_manager & m, ptr_vector<expr> const & constraint, ptr_vector<expr> const & holes)
          : m(m),
            m_constraint(constraint),
            m_holes(holes)
    {}

    app * lemma::get_head_from_holes(func_decl * pred) {
        return m.mk_app(pred, m_holes.size(), m_holes.c_ptr());
    }

    ptr_vector<app> lemma::get_tail_from_holes() {
        ptr_vector<app> new_tail;
        for (ptr_vector<expr>::const_iterator it = m_constraint.begin(); it != m_constraint.end(); ++it) {
            new_tail.push_back(to_app(*it));
        }
        return new_tail;
    }
    void lemma::display(std::ostream & out) {
        out << "constraint:";
        for (unsigned i = 0; i < m_constraint.size(); ++i) {
            out << " " << mk_pp(m_constraint[i], m);
        }
        out << "\n     holes:";
        for (unsigned i = 0; i < m_holes.size(); ++i) {
            out << " " << mk_pp(m_holes[i], m);
        }
        out << "\n";
    }

    rule_ref lemma::enrich_rule(rule & r, vector<unsigned> const & num_rules, rule_set & all_rules) {
        // ptr_vector<sort> sorts;
        // r.get_vars(m, sorts);
        // ptr_vector<app> new_tail;
        // svector<bool> new_tail_neg;
        // new_tail.resize(r.get_tail_size());
        // new_tail_neg.resize(r.get_tail_size());
        // for (unsigned i = 0; i < r.get_tail_size(); ++i) {
        //     new_tail[i] = r.get_tail(i);
        //     new_tail_neg[i] = r.is_neg_tail(i);
        // }
        // vector< ptr_vector<expr> > head;
        // head.resize(num_rules.size());

        // unsigned ind = 0;
        // for (unsigned i = 0; i < num_rules.size(); ++i) {
        //     for (unsigned j = 0; j < num_rules[i]; ++j) {
        //         head[i].push_back(r.get_head()->get_args()[ind++]);
        //     }
        // }
        // unsigned delta = sorts.size();
        // ptr_vector<expr> appendix;
        // ptr_vector<sort> tmp1;
        // svector<symbol> tmp2;
        // fill_holes(false, head, delta, appendix, tmp1, tmp2);
        // for (ptr_vector<expr>::const_iterator it = appendix.begin(); it != appendix.end(); ++it) {
        //     new_tail.push_back(to_app(*it));
        //     new_tail_neg.push_back(false);
        // }

        // rule_manager & rm = all_rules.get_rule_manager();
        // rule_ref new_rule(rm);
        // new_rule = rm.mk(r.get_head(), new_tail.size(), new_tail.c_ptr(), new_tail_neg.c_ptr(), r.name(), false);
        // return new_rule;
    }

    bool lemma::is_empty() {
        if (m_constraint.empty()) {
            return true;
        }
        return true;
    }

    // -----------------------------------
    //
    // transformation
    //
    // -----------------------------------

    mk_synchronize::mk_synchronize(context& ctx, unsigned priority):
        rule_transformer::plugin(priority, false),
        m_ctx(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager()),
        m_solver(m, m_smt_params)
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
        // return true;
    }

    rule * mk_synchronize::get_original_rule(rule * r) const {
        return m_rule2orig.contains(r) ? m_rule2orig[r] : r;
    }

    rule_ref mk_synchronize::replace_applications(rule & r, ptr_vector<app> & apps, func_decl * pred, app *& resulting_app) {
        resulting_app = product_application(apps, pred);

        ptr_vector<app> new_tail;
        svector<bool> new_tail_neg;
        unsigned n = r.get_tail_size() - apps.size() + 1;
        unsigned tail_idx = 0;
        new_tail.resize(n);
        new_tail_neg.resize(n);
        new_tail[0] = resulting_app;
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
            new_tail.c_ptr(), new_tail_neg.c_ptr(), /*symbol("REPLACED APPLICATION")*/r.name(), false);
        m_rule2orig.insert(new_rule.get(), &r);
        return new_rule;
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
        new_rule = rm.mk(r, r->name());
        rm.substitute(new_rule, revsub.size(), revsub.c_ptr());

        rule * result = new_rule.steal();
        m_rule2orig.insert(result, r);
        return result;
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

    lemma * mk_synchronize::mine_lemma_from_rule(rule & r, ptr_vector<app> & apps) const {
        ptr_vector<expr> conjuncts;
        ptr_vector<expr> holes;
        conjuncts.resize(r.get_tail_size() - r.get_uninterpreted_tail_size());
        for (unsigned i = r.get_tail_size(), j = 0; i > r.get_uninterpreted_tail_size(); --i, ++j) {
            conjuncts[j] = r.get_tail(i-1);
        }
        for (ptr_vector<app>::const_iterator it = apps.begin(); it != apps.end(); ++it) {
            holes.append(ptr_vector<expr>((*it)->get_num_args(), (*it)->get_args()));
        }

        return alloc(lemma, m, conjuncts, holes);
    }

    lemma * mk_synchronize::mine_lemma_from_model(expr_ref const & modelr, func_decl * rho) const {
        expr_ref_vector result(m);
        result.push_back(modelr);
        ptr_vector<expr> conjuncts;
        ptr_vector<expr> holes;
        flatten_and(result);
        expr_array r;

        for (expr_ref_vector::iterator it = result.begin(); it != result.end(); ++it) {
            // conjuncts.push_back(*it);
            m.push_back(r, *it);
        }
        expr_array s;
        m.copy(r, s);
        for (unsigned i = 0; i < m.size(s); ++i) {
            conjuncts.push_back(m.get(s, i));
        }
        holes.resize(rho->get_arity());
        for (unsigned i = 0; i < rho->get_arity(); ++i) {
            holes[i] = m.mk_var(i, rho->get_domain(i));
        }
        // holes.push_back(ptr_vector<expr>((*it)->get_num_args(), (*it)->get_args()));

        return alloc(lemma, m, conjuncts, holes);
    }

    void mk_synchronize::update_reachability_graph(func_decl * new_rel, ptr_vector<app> const & apps, rule * old_rule, rule * new_rule, rule_set & rules) {
        obj_hashtable<func_decl> orig_decls;
        for (ptr_vector<app>::const_iterator it = apps.begin(); it != apps.end(); ++it) {
            orig_decls.insert((*it)->get_decl());
        }
        rule_vector const & new_rules = rules.get_predicate_rules(new_rel);
        rule_reachability_graph::item_set const & deps = m_graph->get_deps(old_rule);
        for (rule_vector::const_iterator it = new_rules.begin(); it != new_rules.end(); ++it) {
            rule * prod = *it;
            bool depends = true;
            rule_vector const & orig_rules = *m_prod2orig[prod];
            for (rule_vector::const_iterator it2 = orig_rules.begin(); it2 != orig_rules.end(); ++it2) {
                if (!deps.contains(get_original_rule(*it2))) {
                    depends = false;
                    break;
                }
            }
            if (depends) {
                m_graph->connect(new_rule, prod);
            }
        }
        for (rule_reachability_graph::item_set::iterator it = deps.begin(); it != deps.end(); ++it) {
            if (!orig_decls.contains((*it)->get_head()->get_decl())) {
                m_graph->connect(new_rule, *it);
            }
        }
        m_graph->remove(old_rule);
    }

    void mk_synchronize::update_reachability_graph(func_decl * new_rel, rule_set & rules) {
        rule_vector const & new_rules = rules.get_predicate_rules(new_rel);
        for (rule_vector::const_iterator it = new_rules.begin(); it != new_rules.end(); ++it) {
            rule * prod = *it;
            std::set<rule*> recursive_deps;
            bool initialized_recursive_deps = false;
            rule_vector const & orig_rules = *m_prod2orig[prod];
            for (unsigned i = 0; i < orig_rules.size(); ++i) {
                rule * orig = get_original_rule(orig_rules[i]);
                std::set<rule*> candidate_recursive_deps;
                rule_reachability_graph::item_set const & deps = m_graph->get_deps(orig);
                for (rule_reachability_graph::item_set::iterator it2 = deps.begin(); it2 != deps.end(); ++it2) {
                    rule * dep = *it2;
                    if (dep->get_head()->get_decl() == orig->get_head()->get_decl()) {
                        std::pair<unsigned, rule*> key(i, dep);
                        SASSERT(m_orig2prod.find(key) != m_orig2prod.end());
                        std::set<rule*> products_of_dep = *m_orig2prod[key];
                        candidate_recursive_deps.insert(products_of_dep.begin(), products_of_dep.end());
                    } else {
                        m_graph->connect(prod, dep);
                    }
                }
                if (!initialized_recursive_deps) {
                    recursive_deps = candidate_recursive_deps;
                    initialized_recursive_deps = true;
                } else {
                    std::set<rule*> tmp;
                    set_intersection(recursive_deps.begin(), recursive_deps.end(), candidate_recursive_deps.begin(), candidate_recursive_deps.end(), std::inserter(tmp, tmp.begin()));
                    recursive_deps = tmp;
                }
            }
            for (std::set<rule*>::const_iterator it2 = recursive_deps.begin(); it2 != recursive_deps.end(); ++it2) {
                m_graph->connect(prod, *it2);
            }
        }
    }

    app * mk_synchronize::product_application(ptr_vector<app> const & apps, func_decl * pred) {
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
            }
        }

        return m.mk_app(pred, args_num, args.c_ptr());
    }

    rule_ref mk_synchronize::product_rule(rule_vector const & rules, func_decl * pred) {
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
            // TODO: there may be more than one recursive call!
            ptr_vector<app> unique_recursive_calls;
            unique_recursive_calls.resize(n);
            for (unsigned i = 0; i < n; ++i) {
                unique_recursive_calls[i] = recursive_calls[i][0];
            }

            ++tail_idx;
            new_tail[tail_idx] = product_application(unique_recursive_calls, pred);
            new_tail_neg[tail_idx] = false;
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

    bool mk_synchronize::merge_if_needed(rule & r, ptr_vector<app> & apps, rule_set & all_rules, 
            func_decl * pred) {
        m_stratifier = alloc(reachability_stratifier, *m_graph);

        reachability_stratifier::comp_vector const & strata = m_stratifier->get_strats();

        lemma * source_lemma = mine_lemma_from_rule(r, apps);

        std::cout << "--------------------------------\n";
        std::cout << "a. for stratum ";
        std::cout << "got\n";
        source_lemma->display(std::cout);
        std::cout << "--------------------------------\n";

        vector< vector<unsigned> > merged;
        unsigned n = apps.size();
        merged.resize(n);

        for (unsigned j = 0; j < n; ++j) {
            for (unsigned i = strata.size(); i > 0; --i) {
                reachability_stratifier::item_set & stratum = *strata[i-1];
                if (!stratum.empty() && (*stratum.begin())->get_head()->get_decl() == apps[j]->get_decl()) {
                    merged[j].push_back(i-1);
                }
            }
        }

        vector<unsigned> query_stratum;
        for (unsigned i = strata.size(); i > 0; --i) {
            reachability_stratifier::item_set & stratum = *strata[i-1];
            if (stratum.contains(&r)) {
                for (unsigned j = 0; j < n; ++j) {
                    query_stratum.push_back(i-1);
                }
                break;
            }
        }

        vector2lemma_map strata2lemmas;
        strata2lemmas.insert(query_stratum, source_lemma);

        vector <unsigned> num_args;
        num_args.resize(n);
        ptr_vector<sort> domain;

        for (unsigned i = 0; i < n; ++i) {
            num_args[i] = apps[i]->get_num_args();
            func_decl* decl = apps[i]->get_decl();
            domain.append(decl->get_arity(), decl->get_domain());
        }

        params_ref _p = m_ctx.get_params().p;
        _p.set_bool("datalog.synchronization", false);
        bool tail_simplifier_pve = _p.get_bool("xform.tail_simplifier_pve", true);
        _p.set_bool("xform.tail_simplifier_pve", false);
        m_ctx.updt_params(_p);
        vector<unsigned> stratum_buf;
        stratum_buf.resize(n);
        compute_lemmas(0, merged, stratum_buf, strata2lemmas, strata, domain, num_args);
        std::cout << "out from compute" << std::endl;
        _p.set_bool("datalog.synchronization", true);
        _p.set_bool("xform.tail_simplifier_pve", tail_simplifier_pve);
        m_ctx.updt_params(_p);
        stratum_buf.reset(); stratum_buf.resize(n);
        bool empty = true;
        strata2lemmas.remove(query_stratum);
        for (vector2lemma_map::iterator it = strata2lemmas.begin(); it != strata2lemmas.end(); ++it) {
            if (!((it->m_value)->is_empty())) {
                empty = false;
                break;
            }
        }
        if(!empty) {
            merge(0, merged, stratum_buf, strata2lemmas, all_rules, pred, strata);
            return true;
        }
        return false;
    }

    void mk_synchronize::compute_lemmas(unsigned idx, vector< vector<unsigned> > const & merged_stratum,
        vector<unsigned> & stratum_buf, vector2lemma_map & strata2lemmas,
        reachability_stratifier::comp_vector const & strata, ptr_vector<sort> domain, vector<unsigned> num_args) {
        if (idx >= merged_stratum.size()) {

            bool recursive = false;
            bool has_non_rec = false;
            for (unsigned i = stratum_buf.size(); i > 0; --i) {
                if (!m_stratifier->is_non_recursive_stratum(*strata[stratum_buf[i-1]])) {
                    recursive = true;
                }
                else {
                    has_non_rec = true;
                }
            }
            if (!recursive) {
                return;
            }
            func_decl* rho = m_ctx.mk_fresh_head_predicate(symbol("__rho"),
                symbol::null, domain.size(), domain.c_ptr());
            ptr_vector<lemma> source_lemmas;

            if (!strata2lemmas.empty()) {
                for (vector2lemma_map::iterator it = strata2lemmas.begin(); it != strata2lemmas.end(); ++it) {
                    bool connected = true;
                    for (unsigned i = 0; i < stratum_buf.size(); ++i) {
                        if (!m_stratifier->strata_connected(*strata[(it->m_key)[i]], *strata[stratum_buf[i]])) {
                            connected = false;
                            break;
                        }
                    }
                    if (connected) {
                        (it->m_value)->display(std::cout);
                        source_lemmas.push_back(strata2lemmas[it->m_key]);
                    }
                }
            }

            for (ptr_vector<lemma>::iterator it = source_lemmas.begin(); it != source_lemmas.end(); ++it) {
                app * head = (*it)->get_head_from_holes(rho);
                ptr_vector<app> tail = (*it)->get_tail_from_holes();
                rule_ref new_rule(rm);
                new_rule = rm.mk(head, tail.size(), tail.c_ptr());
                
                // std::cout << "FACT RULES" << std::endl;
                // new_rule.get()->display(m_ctx, std::cout);
                m_ctx.add_rule(new_rule);
            }
            rule_vector rules_buf;
            rules_buf.resize(merged_stratum.size());
            unsigned var_idx = 0;
            add_rules_for_lemma(0, rules_buf, stratum_buf, rho, var_idx, strata);

            app * fail = add_fail_rules(strata, stratum_buf, rho, num_args, has_non_rec);

            m_ctx.display_rules(std::cout);
            std::cout << "QUERY" << std::endl;
            std::cout << mk_pp(fail, m) << std::endl;
            if (m_ctx.query(fail) == l_false) {
                std::cout << "MODEL" << std::endl;
                model_ref model = m_ctx.get_model();
                std::cout << "model" << std::endl;
                expr_ref modelr(m);
                model->eval(rho, modelr);
                lemma * new_lemma = mine_lemma_from_model(modelr, rho);
                std::cout << "--------------------------------\n";
                std::cout << "b. for stratum ";
                std::cout << "got\n";
                new_lemma->display(std::cout);
                std::cout << "--------------------------------\n";

                strata2lemmas.insert(stratum_buf, new_lemma);
            }
            else {
                std::cout << mk_pp(m_ctx.get_answer_as_formula(), m) << std::endl;
            }

            return;
        }

        vector<unsigned> const & pred_rules = merged_stratum[idx];
        for (vector<unsigned>::const_iterator it = pred_rules.begin(); it != pred_rules.end(); ++it) {
            stratum_buf[idx] = *it;
            compute_lemmas(idx + 1, merged_stratum, stratum_buf, strata2lemmas, strata, domain, num_args);
        }
    }

    app * mk_synchronize::add_fail_rules(reachability_stratifier::comp_vector const & strata,
            vector<unsigned> const & merged_rules, func_decl * rho, vector<unsigned> num_args, bool has_non_rec) {
        ptr_vector<sort> domain;
        ptr_vector<expr> fail_args;
        func_decl* fail = m_ctx.mk_fresh_head_predicate(symbol("__fail"),
            symbol::null, 0, domain.c_ptr());
        app * head = m.mk_app(fail, fail_args.size(), fail_args.c_ptr());

        for (unsigned ind = 0; ind < merged_rules.size(); ++ind) {
            reachability_stratifier::item_set & src = *strata[merged_rules[ind]];
            for (obj_hashtable<rule>::iterator it = src.begin(); it != src.end(); ++it) {
                rule* r = *it;
                ptr_vector<sort> sorts;
                r->get_vars(m, sorts);
                unsigned delta = sorts.size();

                vector< ptr_vector<expr> > rec_args;

                bool recursive = false;
                for (unsigned j = 0; j < r->get_positive_tail_size(); ++j) {
                    app* tail = r->get_tail(j);
                    if (is_recursive_app(*r, tail)) {
                        recursive = true;
                        ptr_vector<expr> args;
                        if (has_non_rec) {
                            mk_unfold * m_unfold  = alloc(mk_unfold, m_ctx);
                            rule_set* dst = alloc(rule_set, m_ctx);
                            m_unfold->expand_tail(*r, j, m_ctx.get_rules(), *dst);
                            rule_set::iterator it = dst->begin(), end = dst->end();
                            for (; it != end; ++it) {
                                (*it)->display(m_ctx, std::cout);
                            }
                        }
                        for (unsigned k = 0; k < tail->get_num_args(); ++k) {
                            args.push_back(tail->get_arg(k));
                        }
                        rec_args.push_back(args);
                    }
                }
                if (recursive) {
                    string_buffer<> buffer;
                    buffer << r->name();
                    buffer << "_";
                    buffer << ind;
                    buffer << "_";
                    unsigned n = rec_args.size();
                    for (unsigned j = 0; j < n; ++j) {
                        buffer << j;
                        ptr_vector<app> new_tail;
                        svector<bool> new_tail_neg;

                        for (unsigned i = 0; i < r->get_positive_tail_size(); ++i) {
                            app* tail = r->get_tail(i);
                            if (!is_recursive_app(*r, tail)) {
                                new_tail.push_back(tail);
                                new_tail_neg.push_back(false);
                            }
                        }

                        ptr_vector<expr> args_rec;
                        ptr_vector<expr> args_non_rec;
                        args_rec.resize(rho->get_arity());
                        args_non_rec.resize(rho->get_arity());

                        unsigned args_ind = 0;
                        for (unsigned i = 0; i < num_args.size(); ++i) {
                            if (ind == i) {
                                for (unsigned k = 0; k < num_args[i]; ++k) {
                                    args_rec[args_ind] = rec_args[j][k];
                                    args_non_rec[args_ind] = r->get_head()->get_arg(k);
                                    ++args_ind;
                                }
                            }
                            else {
                                for (unsigned k = 0; k < num_args[i]; ++k) {
                                    var * unchangeable_var = m.mk_var(delta, rho->get_domain(args_ind));
                                    args_rec[args_ind] = unchangeable_var;
                                    args_non_rec[args_ind] = unchangeable_var;
                                    delta++;
                                    args_ind++;
                                }
                            }
                        }
                        new_tail.push_back(m.mk_app(rho, args_rec.size(), args_rec.c_ptr()));
                        new_tail_neg.push_back(false);

                        new_tail.push_back(m.mk_app(rho, args_non_rec.size(), args_non_rec.c_ptr()));
                        new_tail_neg.push_back(false);

                        for (unsigned i = r->get_positive_tail_size(); i < r->get_uninterpreted_tail_size(); ++i) {
                            new_tail.push_back(r->get_tail(i));
                            new_tail_neg.push_back(true);
                        }
                        for (unsigned i = r->get_uninterpreted_tail_size(); i < r->get_tail_size(); ++i) {
                            new_tail.push_back(r->get_tail(i));
                            new_tail_neg.push_back(r->is_neg_tail(i));
                        }
                        buffer << "__fail";
                        rule_ref new_rule(rm);
                        new_rule = rm.mk(head, new_tail.size(), new_tail.c_ptr(), new_tail_neg.c_ptr(), symbol(buffer.c_str()), false);
                        m_ctx.add_rule(new_rule);
                    }
                }
            }
        }
        return head;
    }

    void mk_synchronize::product_lemma_rule(rule_vector const & rules, func_decl * rho) {
        unsigned n = rules.size();
        ptr_vector<app> new_tail;
        svector<bool> new_tail_neg;

        ptr_vector<app> heads;
        vector< vector< ptr_vector<expr> > >head_args;
        head_args.resize(n);
        unsigned ind = 0;
        unsigned args_num = rho->get_arity();
        ptr_vector<expr> args_tail;
        args_tail.resize(args_num);

        for (unsigned j = 0; j < n; ++j) {
            rule& rule = *rules[j];
            for (unsigned i = 0; i < rule.get_head()->get_num_args(); ++i) {
                args_tail[ind] = rule.get_head()->get_arg(i);
                ind++;
            } 
        }
        new_tail.push_back(m.mk_app(rho, args_num, args_tail.c_ptr()));
        new_tail_neg.push_back(false);

        for (unsigned j = 0; j < n; ++j) {
            rule& rule = *rules[j];
            for (unsigned i = 0; i < rule.get_positive_tail_size(); ++i) {
                app* tail = rule.get_tail(i);
                if (!is_recursive_app(rule, tail)) {
                    new_tail.push_back(tail);
                    new_tail_neg.push_back(false);
                }
                else {
                    ptr_vector<expr> args;
                    for (unsigned k = 0; k < tail->get_num_args(); ++k) {
                        args.push_back(tail->get_arg(k));
                    }
                    head_args[j].push_back(args);
                }
            }
            if (head_args[j].empty()) {
                ptr_vector<expr> args;
                for (unsigned k = 0; k < rule.get_head()->get_num_args(); ++k) {
                    args.push_back(rule.get_head()->get_arg(k));
                }
                head_args[j].push_back(args);
            }

            for (unsigned i = rule.get_positive_tail_size(); i < rule.get_uninterpreted_tail_size(); ++i) {
                new_tail.push_back(rule.get_tail(i));
                new_tail_neg.push_back(true);
            }
            for (unsigned i = rule.get_uninterpreted_tail_size(); i < rule.get_tail_size(); ++i) {
                new_tail.push_back(rule.get_tail(i));
                new_tail_neg.push_back(rule.is_neg_tail(i));
            }
        }
        vector<ptr_vector<expr> > args_buf;
        args_buf.resize(head_args.size());
        add_with_recursive_calls(0, head_args, args_buf, rho, new_tail, new_tail_neg);
        // ptr_vector<expr> args_head;
        // for (unsigned i = 0; i < head_args.size(); ++i) {
        //     for (unsigned j = 0; j < head_args[i][0].size(); ++j){
        //         args_head.push_back(head_args[i][0][j]);
        //     }
        // }
        // app * head = m.mk_app(rho, args_num, args_head.c_ptr());
        // rule_ref new_rule(rm);
        // new_rule = rm.mk(head, new_tail.size(), new_tail.c_ptr(), new_tail_neg.c_ptr());
        // new_rule.get()->display(m_ctx, std::cout);
        // m_ctx.add_rule(new_rule);
        return;
    }

    void mk_synchronize::add_with_recursive_calls(unsigned idx, vector< vector<ptr_vector<expr> > > const & args,
            vector<ptr_vector<expr> > & args_buf, func_decl * rho, ptr_vector<app> tail, svector<bool> tail_neg) {
         if (idx >= args.size()) {
            ptr_vector<expr> args_head;
            for (unsigned i = 0; i < args_buf.size(); ++i) {
                args_head.append(args_buf[i]);
            }
            app * head = m.mk_app(rho, args_head.size(), args_head.c_ptr());
            rule_ref new_rule(rm);
            new_rule = rm.mk(head, tail.size(), tail.c_ptr(), tail_neg.c_ptr());
            // new_rule.get()->display(m_ctx, std::cout);
            m_ctx.add_rule(new_rule);
            return;
        }

        vector<ptr_vector<expr> > const & pred = args[idx];
        for (vector<ptr_vector<expr> >::const_iterator it = pred.begin(); it != pred.end(); ++it) {
            args_buf[idx] = *it;
            add_with_recursive_calls(idx + 1, args, args_buf, rho, tail, tail_neg);
        }
    }

    void mk_synchronize::add_rules_for_lemma(unsigned idx, rule_vector &buf, vector<unsigned> const & merged_rules,
         func_decl * rho, unsigned & var_idx,
         reachability_stratifier::comp_vector const & strata) {
        if (idx >= merged_rules.size()) {
            rule_vector renamed_rules;
            renamed_rules.resize(buf.size());
            for (unsigned i = 0; i < buf.size(); ++i) {
                renamed_rules[i] = rename_bound_vars_in_rule(buf[i], var_idx);
            }
            product_lemma_rule(renamed_rules, rho);
            
            // m_ctx.add_rule(product);
            return;
        }

        obj_hashtable<rule> & pred_rules = *strata[merged_rules[idx]];
        for (obj_hashtable<rule>::iterator it = pred_rules.begin(); it != pred_rules.end(); ++it) {
            buf[idx] = *it;
            add_rules_for_lemma(idx + 1, buf, merged_rules, rho, var_idx, strata);
        }
    }

    void mk_synchronize::merge(unsigned idx, vector< vector<unsigned> > const & merged_stratum,
            vector<unsigned> & stratum_buf,  vector2lemma_map & strata2lemmas,
            rule_set & all_rules, func_decl * pred, reachability_stratifier::comp_vector const & strata) {
         if (idx >= merged_stratum.size()) {
            lemma *source_lemma = NULL;
            if (strata2lemmas.contains(stratum_buf)) {
                source_lemma = strata2lemmas[stratum_buf];
            }
            rule_vector rules_buf;
            rules_buf.resize(merged_stratum.size());
            // if (source_lemma != NULL) {
            //     std::cout << "LEMMA FOR MERGE" << std::endl;
            //     source_lemma->display(std::cout);
            // }
            unsigned var_idx = 0;
            merge_rules(0, rules_buf, stratum_buf, all_rules, pred, *source_lemma, var_idx, strata);
            return;
        }

        vector<unsigned> const & pred_stratum = merged_stratum[idx];
        for (vector<unsigned>::const_iterator it = pred_stratum.begin(); it != pred_stratum.end(); ++it) {
            stratum_buf[idx] = *it;
            merge(idx + 1, merged_stratum, stratum_buf, strata2lemmas, all_rules, pred, strata);
        }
    }                                                                                         \

    void mk_synchronize::merge_rules(unsigned idx, rule_vector &buf, vector<unsigned> const & merged_rules,
         rule_set & all_rules, func_decl * pred, lemma & source_lemma, unsigned & var_idx,
         reachability_stratifier::comp_vector const & strata) {
        if (idx >= merged_rules.size()) {
            // //----
            // bool all_tauto = true;
            // for (unsigned i = 0; i < buf.size(); ++i) {
            //     if (buf[i]->name() != "TAUTO") {
            //         all_tauto = false;
            //         break;
            //     }
            // }
            // if (!all_tauto) {
            //----
            rule_vector renamed_rules;
            vector <unsigned> v;
            renamed_rules.resize(buf.size());
            v.resize(buf.size());
            for (unsigned i = 0; i < buf.size(); ++i) {
                renamed_rules[i] = rename_bound_vars_in_rule(buf[i], var_idx);
                v[i] = buf[i]->get_head()->get_num_args();
            }
            rule_ref product = product_rule(renamed_rules, pred);
            if (&source_lemma != NULL) {
                // product = source_lemma.enrich_rule(*product.get(), v, all_rules);
            }

            m_prod2orig.insert(product.get(), alloc(rule_vector, renamed_rules));
            for (unsigned i = 0; i < renamed_rules.size(); ++i) {
                std::pair<unsigned, rule*> key(i, get_original_rule(renamed_rules[i]));
                std::set<rule*>* prods = 0;
                std::map<std::pair<unsigned, rule*>, std::set<rule*> *>::iterator e = m_orig2prod.find(key);
                if (e == m_orig2prod.end()) {
                    prods = alloc(std::set<rule*>);
                    m_orig2prod.insert(e, std::pair<std::pair<unsigned, rule*>, std::set<rule*>*>(key, prods));
                } else {
                    prods = m_orig2prod[key];
                }
                prods->insert(product.get());
            }
            all_rules.add_rule(product.get());
            return;
        }//}

        obj_hashtable<rule> & pred_rules = *strata[merged_rules[idx]];
        for (obj_hashtable<rule>::iterator it = pred_rules.begin(); it != pred_rules.end(); ++it) {
            buf[idx] = *it;
            merge_rules(idx + 1, buf, merged_rules, all_rules, pred, source_lemma, var_idx, strata);
        }
    }

    void mk_synchronize::merge_applications(rule & r, rule_set & rules) {
        ptr_vector<app> non_recursive_applications;
        for (unsigned i = 0; i < r.get_positive_tail_size(); ++i) {
            app* application = r.get_tail(i);
            if (!is_recursive_app(r, application) && exists_recursive(application, rules)) {
                non_recursive_applications.push_back(application);
            }
        }
        if (non_recursive_applications.size() < 2) {
            return;
        }

        printf("MERGING %d APPLICATIONS...\n", non_recursive_applications.size());
        string_buffer<> buffer;
        ptr_vector<sort> domain;
        ptr_vector<app>::const_iterator it = non_recursive_applications.begin(), end = non_recursive_applications.end();
        for (; it != end; ++it) {
            func_decl* decl = (*it)->get_decl();
            buffer << decl->get_name();
            buffer << "!!";
            domain.append(decl->get_arity(), decl->get_domain());
        }

        // TODO: do not forget to check rules.contains(func_decl)
        func_decl* orig = non_recursive_applications[0]->get_decl();
        func_decl* product_pred = m_ctx.mk_fresh_head_predicate(symbol(buffer.c_str()),
            symbol::null, domain.size(), domain.c_ptr(), orig);

        rule_vector rules_buf;
        unsigned n = non_recursive_applications.size();
        rules_buf.resize(n);

        app * replacing_app;
        if (merge_if_needed(r, non_recursive_applications, rules, product_pred)) {
            printf("MERGE\n");
            r.display(m_ctx, std::cout);
            std::cout << std::endl;
            rule_ref result = replace_applications(r, non_recursive_applications, product_pred, replacing_app);
            update_reachability_graph(product_pred, rules);
            update_reachability_graph(product_pred, non_recursive_applications, &r, result.get(), rules);
            rules.replace_rule(&r, result.get());

            reset_dealloc_values(m_prod2orig);
            for (std::map<std::pair<unsigned, rule*>, std::set<rule*> *>::const_iterator it = m_orig2prod.begin(); it != m_orig2prod.end(); ++it) {
                dealloc(it->second);
            }
            m_orig2prod.clear();
        }
    }

    void mk_synchronize::tautologically_extend(rule_set & rules, ptr_vector<func_decl> const & decls) {
        for (ptr_vector<func_decl>::const_iterator it = decls.begin(); it != decls.end(); ++it) {
            func_decl * d = *it;
            ptr_vector<expr> args;
            args.resize(d->get_arity());
            for (unsigned i = 0; i < d->get_arity(); ++i) {
                sort * s = d->get_domain(i);
                args[i] = m.mk_var(i, s);
            }
            app * premise = m.mk_app(d, args.size(), args.c_ptr());
            app * conclusion = m.mk_app(d, args.size(), args.c_ptr());
            bool neg = false;
            rule_ref new_rule(rm);
            new_rule = rm.mk(conclusion, 1, &premise, &neg, symbol("TAUTO"), false);
            rules.add_rule(new_rule.get());
        }
    }

    rule_set * mk_synchronize::operator()(rule_set const & source) {
        printf("\n\n----------------------------------\nSYNCHRONIZING! SOURCE RULES:\n");
        source.display(std::cout);

        rule_set* rules = alloc(rule_set, m_ctx);
        rules->inherit_predicates(source);

        rule_set::iterator it = source.begin(), end = source.end();
        for (; it != end; ++it) {
            rules->add_rule(*it);
        }

        m_graph = alloc(rule_reachability_graph, m_ctx, *rules);

        // ptr_vector<func_decl> decls;
        // for (rule_set::decl2rules::iterator it = rules->begin_grouped_rules(); it != rules->end_grouped_rules(); ++it) {
        //     decls.push_back(it->m_key);
        // }
        // tautologically_extend(*rules, decls);

        unsigned current_rule = 0;

        while (current_rule < rules->get_num_rules()) {
            rule *r = rules->get_rule(current_rule);
            merge_applications(*r, *rules);
            ++current_rule;
        }

        // printf("\n-----------------DEPENDENCIES GRAPH-----------------\n");
        // m_stratifier = alloc(reachability_stratifier, *m_graph);
        // m_stratifier->display(std::cout);
        // if (!m_stratifier->validate_mutual_recursion()) {
        //     return rules;
        // }
        // printf("\n------------------------------------------------------------\n");

        printf("\n\n-----------------RESULTING RULES:-----------------\n");
        rules->display(std::cout);
        printf("\n\n----------------------------------\n");
        return rules;
    }

};
