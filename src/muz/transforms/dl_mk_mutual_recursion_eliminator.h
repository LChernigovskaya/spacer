

#ifndef DL_MK_MUTUAL_RECURSION_ELIMINATOR_H
#define DL_MK_MUTUAL_RECURSION_ELIMINATOR_H

#include"dl_context.h"
#include"dl_rule_set.h"
#include"dl_rule_transformer.h"
#include"dl_rule_dependencies.h"
#include"arith_decl_plugin.h"


namespace datalog {

    /**
       \brief Implements an unfolding transformation.
    */
    class mk_mutual_recursion_eliminator : public rule_transformer::plugin {
        context&        m_ctx;
        ast_manager&    m;
        rule_manager&   rm;
        arith_util      m_autil;
        void merge_mutual_recursion(rule & r, rule_set & rules);

    public:
        mk_mutual_recursion_eliminator(context & ctx, unsigned priority);

        rule_set * operator()(rule_set const & source);
    };

};

#endif /* DL_MK_MUTUAL_RECURSION_ELIMINATOR_H */
