

#ifndef DL_MK_MUTUAL_RECURSION_ELIMINATOR_H
#define DL_MK_MUTUAL_RECURSION_ELIMINATOR_H

#include"dl_context.h"
#include"dl_rule_set.h"
#include"dl_rule_transformer.h"
#include"dl_rule_dependencies.h"
#include"arith_decl_plugin.h"


namespace datalog {

    /**
       \brief Implements a elimination of mutual recursion transformation.
    */
    class mk_mutual_recursion_eliminator : public rule_transformer::plugin {
        context&        m_ctx;
        ast_manager&    m;
        rule_manager&   rm;
        arith_util      m_autil;
        void merge_mutual_recursion(rule_set & rules);
        void merge_mutual_in_tails(rule_set & rules, ptr_vector<func_decl> mutual_functions,
			obj_map<func_decl, unsigned>, func_decl * product_pred);
        bool contains_one_of_functions_in_tail(rule & r, ptr_vector<func_decl> functions);
        void merge_mutual_in_heads(rule_set & rules, ptr_vector<func_decl> mutual_functions,
			obj_map<func_decl, unsigned> m_func2arg, func_decl * product_pred);

    public:
        mk_mutual_recursion_eliminator(context & ctx, unsigned priority);

        rule_set * operator()(rule_set const & source);
    };

};

#endif /* DL_MK_MUTUAL_RECURSION_ELIMINATOR_H */
