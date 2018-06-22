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

#include"dl_context.h"
#include"dl_rule_set.h"
#include"uint_set.h"
#include"dl_rule_transformer.h"
#include"dl_mk_rule_inliner.h"

namespace datalog {

    /**
       \brief Implements a synchronous product transformation.
    */
    class mk_synchronize : public rule_transformer::plugin {
        context&        m_ctx;
        ast_manager&    m;
        rule_manager&   rm;

        scoped_ptr<rule_dependencies> m_deps;
        scoped_ptr<rule_stratifier> m_stratifier;
        map<symbol, func_decl*, symbol_hash_proc, symbol_eq_proc> cache;

        struct app_compare {
            bool operator()(app* a, app* b) const {
                return a->get_decl()->get_name() > b->get_decl()->get_name();
            }
        };

        bool is_recursive_app(rule & r, app * app) const;
        bool exists_recursive(app * app) const;

        ptr_vector<rule_stratifier::item_set> add_merged_decls(ptr_vector<app> apps);
        void add_new_rel_symbol (unsigned idx, ptr_vector<rule_stratifier::item_set> const & decls,
            ptr_vector<func_decl> & buf, bool & was_added);

        void replace_applications(rule & r, rule_set & rules, ptr_vector<app> & apps);

        rule * rename_bound_vars_in_rule(rule * r, unsigned & var_idx);
        vector<rule_vector> rename_bound_vars(ptr_vector<rule_stratifier::item_set> const & heads, rule_set & rules);

        app* product_application(ptr_vector<app> const & apps);
        rule_ref product_rule(rule_vector const & rules);

        void merge_rules(unsigned idx, rule_vector & buf,
            vector<rule_vector> const & merged_rules, rule_set & all_rules);
        void merge_applications(rule & r, rule_set & rules);

    public:
        /**
           \brief Create synchronous product transformer.
         */
        mk_synchronize(context & ctx, unsigned priority = 22500);

        rule_set * operator()(rule_set const & source);
    };

};

#endif /* DL_MK_SYNCHRONIZE_H_ */

