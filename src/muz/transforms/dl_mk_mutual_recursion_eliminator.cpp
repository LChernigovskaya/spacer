#include "dl_mk_mutual_recursion_eliminator.h"

namespace datalog {

	mk_mutual_recursion_eliminator::mk_mutual_recursion_eliminator(context& ctx, unsigned priority):
        rule_transformer::plugin(priority, false),
        m_ctx(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager()),
        m_autil(m)
    {}

    // void mk_mutual_recursion_eliminator::merge_mutual_recursion(rule & r, rule_set & rules) {
    	// for (unsigned i = 0; i < r.get_positive_tail_size(); ++i) {
     //        app* application = r.get_tail(i);
     //        if (!is_recursive_app(r, application) && exists_recursive(application, rules)) {
     //            non_recursive_applications.push_back(application);
     //        }
     //    }
    // }

    rule_set * mk_mutual_recursion_eliminator::operator()(rule_set const & source) {
        printf("\n\n----------------------------------\nSYNCHRONIZING! SOURCE RULES:\n");
        source.display(std::cout);

        rule_set* rules = alloc(rule_set, m_ctx);
        rules->inherit_predicates(source);

        rule_set::iterator it = source.begin(), end = source.end();
        for (; it != end; ++it) {
            rules->add_rule(*it);
        }
        // unsigned current_rule = 0;

        // while (current_rule < rules->get_num_rules()) {
        //     rule *r = rules->get_rule(current_rule);
        //     merge_mutual_recursion(*r, *rules);
        //     ++current_rule;
        // }
        if (rules->close()) {
        	std::cout << "dependencies" << std::endl;
        	rules->get_dependencies().display(std::cout);
        	std::cout << "deps" << std::endl;
        	rules->display_deps(std::cout);
        	rule_set::pred_set_vector const &strats = rules->get_strats();
	        for (unsigned i = 1; i < strats.size(); ++i) {
            	func_decl_set::iterator it = strats[i]->begin(), end = strats[i]->end();
            	func_decl * head;
            	bool is_mutual = false;
            	string_buffer<> buffer;
        		ptr_vector<sort> domain;
        		ptr_vector<func_decl> mutual_functions;
            	if (it != end) {
	                head = *it;
	                buffer << head->get_name();
	                domain.append(head->get_arity(), head->get_domain());
	                mutual_functions.push_back(head);
	            }
	            for (; it != end; ++it) {
	                func_decl* pred = *it;
	                if (pred != head) {
	                	is_mutual = true;
	                	buffer << "+";
	                	buffer << pred->get_name();
	                	std::cout << "mutual" << std::endl;
	                	std::cout << head->get_name() << std::endl;
	                	std::cout << pred->get_name() << std::endl;
            			mutual_functions.push_back(pred);
	                }
            	}

            	if (is_mutual) {
					symbol name = symbol(buffer.c_str());
					std::cout << name << std::endl;
					std::cout << domain.size() << std::endl;
					var* new_var = m.mk_var(domain.size(), m.mk_sort(symbol("Int"), sort_info(*m.get_sort(m_autil.mk_int(0))->get_info())));
					std::cout << new_var->get_sort()->get_decl_kind() << std::endl;
					domain.push_back(new_var->get_sort());
			        func_decl* product_pred = m_ctx.mk_fresh_head_predicate(name,
			        	symbol::null, domain.size(), domain.c_ptr(), head);
			        std::cout << product_pred->get_name() << std::endl;
			        for (unsigned n = 0; n < mutual_functions.size(); ++n) {	
			        	rule_vector const & src_rules = rules->get_predicate_rules(mutual_functions[n]);
			        	for (rule_vector::const_iterator it = src_rules.begin(); it != src_rules.end(); ++it) {
			        		rule* rule = (*it);
			        		unsigned args_num = rule->get_head()->get_num_args() + 1;
			        		ptr_vector<expr> args;
				        	args.resize(args_num);
				        	for (unsigned i = 0; i < args_num - 1; ++i) {
				                args[i] = rule->get_head()->get_arg(i);
				            }
				            
				            args[args_num - 1] = new_var;
				            std::cout << "var" << std::endl;
			        		app* new_head = m.mk_app(product_pred, args_num, args.c_ptr());
			        		std::cout << "var" << std::endl;

					        ptr_vector<app> new_tail;
					        svector<bool> new_tail_neg;
					        new_tail.resize(rule->get_tail_size() + 1);
					        new_tail_neg.resize(rule->get_tail_size() + 1);
					        unsigned tail_idx = 0;
				            for (unsigned j = 0; j < rule->get_positive_tail_size(); ++j) {
				                app* tail = rule->get_tail(j); 
			                    new_tail[tail_idx] = tail;
			                    new_tail_neg[tail_idx] = false;
			                    ++tail_idx;
				            }
				            for (unsigned j = rule->get_positive_tail_size(); j < rule->get_uninterpreted_tail_size(); ++j) {
				                new_tail[tail_idx] = rule->get_tail(j);
				                new_tail_neg[tail_idx] = true;
				                ++tail_idx;
				            }
				            for (unsigned j = rule->get_uninterpreted_tail_size(); j < rule->get_tail_size(); ++j) {
				                new_tail[tail_idx] = rule->get_tail(j);
				                new_tail_neg[tail_idx] = rule->is_neg_tail(j);
				                ++tail_idx;
				            }
				            std::cout << "NEW TAIL BEGIN" << std::endl;
				            std::cout << m_autil.mk_int(n)->get_decl_kind() << std::endl;
				            std::cout << mk_pp(new_var->get_sort(), m) << " " << mk_pp(m.get_sort(m_autil.mk_int(n)), m) << std::endl;
				            new_tail[tail_idx] = m_autil.mk_eq(new_var, m_autil.mk_int(n));
				            std::cout << "NEW TAIL" << std::endl;
				            std::cout << mk_pp(new_tail[tail_idx], m) << std::endl;
				            rule_ref new_rule(rm);
					        new_rule = rm.mk(new_head, tail_idx + 1,
					            new_tail.c_ptr(), new_tail_neg.c_ptr(), symbol(buffer.c_str()), false);
					        rm.fix_unbound_vars(new_rule, false);
			        	}

				        
			        }
			    }
        	}
        }
        rules->reopen();
        return rules;
    }

};