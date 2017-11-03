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
#ifndef DL_MK_SYNCHRONIZE_H_
#define DL_MK_SYNCHRONIZE_H_

#include<set>
#include<map>
#include"dl_context.h"
#include"dl_rule_set.h"
#include"uint_set.h"
#include"dl_rule_transformer.h"
#include"dl_rule_dependencies.h"
#include"dl_mk_rule_inliner.h"
#include"smt_kernel.h"

namespace datalog {

    class rule_reachability_graph : public rule_dependencies_base<rule> {
        rule_set const & m_rules;
        rule_unifier     m_unify;

        virtual void populate_one(rule * r);
        bool check_reachability(rule & src, unsigned tail_idx, rule & dst, rule_ref & tmp);

    public:
        rule_reachability_graph(context & ctx, rule_set const & rules);
        ~rule_reachability_graph();

        void connect(rule * r1, rule * r2);

        void display( std::ostream & out ) const;
    };

    class reachability_stratifier : public rule_stratifier_base<rule> {
    private:
        const rule_reachability_graph & m_graph;
    public:
        reachability_stratifier(rule_reachability_graph const & graph);
        ~reachability_stratifier();

        bool validate_mutual_recursion() const;
        void display( std::ostream & out ) const;

        bool strata_connected(item_set & src, item_set & dst) const;
        bool is_non_recursive_stratum(item_set & s) const;
    };

    class lemma {
        ast_manager & m;
        ptr_vector<expr> m_constraint;
        vector< ptr_vector<expr> > m_holes;
        vector< svector<bool> > m_hole_enabled;

        void replace_bound_vars_in_this(bool with_consts, unsigned & delta, ptr_vector<expr> & new_constraint,
            vector< ptr_vector<expr> > & new_holes, ptr_vector<sort> & var_sorts, svector<symbol> & var_names);
        void fill_holes(bool replace_with_consts, vector< ptr_vector<expr> > exprs, unsigned & delta,
            ptr_vector<expr> & result, ptr_vector<sort> & var_sorts, svector<symbol> & var_names);
        void helper(unsigned idx, rule_vector &buf, vector<unsigned> const & merged_rules,
        expr_ref_vector & result, vector<ptr_vector<expr> > & head_implicants, vector<ptr_vector<expr> > & call_implicants,
        unsigned & delta, ptr_vector<sort> & free_var_sorts, svector<symbol> & free_var_names,
        reachability_stratifier::comp_vector const & strata);

    public:
        lemma(ast_manager & m, ptr_vector<expr> const & constraint, vector< ptr_vector<expr> > const & holes);
        lemma(ast_manager & m, ptr_vector<lemma> const & combined_lemmas);
        lemma(ast_manager & m, lemma & source, ptr_vector<expr> const & old_assumption_vars, obj_hashtable<expr> const & new_assumption_vars);

        expr_ref_vector operator()(vector<unsigned> const & merged_stratum, ptr_vector<expr> & assumption_vars,
            ptr_vector<expr> & conclusions, ptr_vector<sort> & free_var_sorts, svector<symbol> & free_var_names,
            reachability_stratifier::comp_vector const & strata);

        rule_ref enrich_rule(rule & r, vector<unsigned> const & num_rules, rule_set & all_rules);

        void display( std::ostream & out );

        bool is_empty();
    };

    /**
       \brief Implements a synchronous product transformation.
    */
    class mk_synchronize : public rule_transformer::plugin {
        template<class T>
        struct vector_hash_proc {
            unsigned operator()(const vector<typename T::data> & cont) const {
                return vector_hash<T>()(cont);
            }
        };
        typedef map<vector<unsigned>, lemma*, vector_hash_proc<unsigned_hash>, vector_eq_proc< vector<unsigned> > > vector2lemma_map;
        typedef obj_hashtable<expr> expr_set;
        context&        m_ctx;
        ast_manager&    m;
        rule_manager&   rm;
        smt_params  m_smt_params;
        smt::kernel m_solver;
        scoped_ptr<rule_reachability_graph> m_graph;
        scoped_ptr<reachability_stratifier> m_stratifier;
        obj_map<rule, rule*> m_rule2orig;
        std::map<std::pair<unsigned, rule*>, std::set<rule*> *> m_orig2prod;
        obj_map<rule, rule_vector*> m_prod2orig;

        bool is_recursive_app(rule & r, app * app) const;
        bool exists_recursive(app * app, rule_set & rules) const;
        rule * get_original_rule(rule * r) const;

        rule * rename_bound_vars_in_rule(rule * r, unsigned & var_idx);
        vector<rule_vector> rename_bound_vars(ptr_vector<func_decl> const & heads, rule_set & rules);
        rule_ref replace_applications(rule & r, ptr_vector<app> & apps, func_decl * pred, app *& resulting_app);

        lemma * mine_lemma_from_rule(rule & r, ptr_vector<app> & apps) const;
        obj_hashtable<expr> extract_invariant(expr_ref_vector const & constraint, ptr_vector<expr> const & assumption_vars,
                ptr_vector<expr> const & conclusions, ptr_vector<sort> const & free_var_sorts, svector<symbol> const & free_var_names);
        void disable_minimal_unsatisfiable_subset(expr_ref_vector const & set, model_ref const & model, svector<bool> & enabled);
        void update_reachability_graph(func_decl * new_rel, ptr_vector<app> const & apps, rule * old_rule, rule * new_rule, rule_set & rules);
        void update_reachability_graph(func_decl * new_rel, rule_set & rules);

        app* product_application(ptr_vector<app> const & apps, func_decl * pred);
        rule_ref product_rule(rule_vector const & rules, func_decl * pred);

        bool merge_if_needed(rule & r, ptr_vector<app> & apps, rule_set & all_rules, func_decl * pred, unsigned current_lemma);
        void compute_lemmas(unsigned idx, vector< vector<unsigned> > const & merged_stratum, vector<unsigned> & stratum_buf,
        lemma & source_lemma, vector2lemma_map & strata2lemmas,
        reachability_stratifier::comp_vector const & strata);
        void merge_rules(unsigned idx, rule_vector &buf, vector<unsigned> const & merged_rules,
         rule_set & all_rules, func_decl * pred, lemma & source_lemma, unsigned & var_idx,
         reachability_stratifier::comp_vector const & strata);
        void merge_applications(rule & r, rule_set & rules, unsigned current_lemma);
        void tautologically_extend(rule_set & rules, ptr_vector<func_decl> const & decls);
        void merge(unsigned idx, vector< vector<unsigned> > const & merged_stratum,
            vector<unsigned> & stratum_buf, vector2lemma_map & strata2lemmas,
            rule_set & all_rules, func_decl * pred, reachability_stratifier::comp_vector const & strata);

    public:
        /**
           \brief Create synchronous product transformer.
         */
        mk_synchronize(context & ctx, unsigned priority = 22500);

        rule_set * operator()(rule_set const & source);
    };

};

#endif /* DL_MK_SYNCHRONIZE_H_ */

