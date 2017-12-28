#include "dl_mk_mutual_recursion_eliminator.h"

namespace datalog {

	mk_mutual_recursion_eliminator::mk_mutual_recursion_eliminator(context& ctx, unsigned priority):
        rule_transformer::plugin(priority, false),
        m_ctx(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager()),
        m_autil(m)
    {}

    void mk_mutual_recursion_eliminator::merge_mutual_in_heads(rule_set & rules, ptr_vector<func_decl> mutual_functions,
		obj_map<func_decl, unsigned> m_func2arg, func_decl * product_pred) {
		unsigned number_functions = mutual_functions.size();
		for (unsigned n = 0; n < number_functions; ++n) {
			rule_vector const & src_rules = rules.get_predicate_rules(mutual_functions[n]);
			for (rule_vector::const_iterator it = src_rules.begin(); it != src_rules.end(); ++it) {
				rule* rule = (*it);
				unsigned args_num = product_pred->get_arity();
				ptr_vector<expr> args;
				args.resize(args_num);
				unsigned ind = 0;
				for (unsigned i = 0; i < n; ++i) {
					for (unsigned j = 0; j < m_func2arg[mutual_functions[i]]; ++j) {
						args[ind] = m.mk_fresh_const("__av", product_pred->get_domain(ind));
						++ind;
					}
				}
				for (unsigned i = 0; i < m_func2arg[mutual_functions[n]]; ++i) {
					args[ind] = rule->get_head()->get_arg(i);
					++ind;
				}

				for (unsigned i = n + 1; i < number_functions; ++i) {
					for (unsigned j = 0; j < m_func2arg[mutual_functions[i]]; ++j) {
						args[ind] = m.mk_fresh_const("__av", product_pred->get_domain(ind));
						++ind;
					}
				}
				// std::cout << (ind == (args_num - 1)) << std::endl;
				args[ind] = m_autil.mk_int(n);
				// std::cout << "var" << std::endl;
				app* new_head = m.mk_app(product_pred, args_num, args.c_ptr());
				// std::cout << new_head->get_num_args() << std::endl;
				// std::cout << mk_pp(new_head, m) << std::endl;

				ptr_vector<app> new_tail;
				svector<bool> new_tail_neg;
				new_tail.resize(rule->get_tail_size());
				new_tail_neg.resize(rule->get_tail_size());
				unsigned tail_idx = 0;
				for (unsigned current_tail = 0; current_tail < rule->get_uninterpreted_tail_size(); ++current_tail) {
					app* tail = rule->get_tail(current_tail);
					for (unsigned n1 = 0; n1 < mutual_functions.size(); ++n1) {
						if (mutual_functions[n1] == tail->get_decl()) {
							unsigned args_num = product_pred->get_arity();
							ptr_vector<expr> args;
							args.resize(args_num);

							unsigned ind = 0;
							for (unsigned i = 0; i < n1; ++i) {
								for (unsigned j = 0; j < m_func2arg[mutual_functions[i]]; ++j) {
									args[ind] = m.mk_fresh_const("__av", product_pred->get_domain(ind));
									++ind;
								}
							}
							for (unsigned i = 0; i < m_func2arg[mutual_functions[n1]]; ++i) {
								args[ind] = tail->get_arg(i);
								++ind;
							}

							for (unsigned i = n1 + 1; i < mutual_functions.size(); ++i) {
								for (unsigned j = 0; j < m_func2arg[mutual_functions[i]]; ++j) {
									args[ind] = m.mk_fresh_const("__av", product_pred->get_domain(ind));
									++ind;
								}
							}
							args[ind] = m_autil.mk_int(n1);
							// std::cout << "new_tail" << std::endl;
							tail = m.mk_app(product_pred, args_num, args.c_ptr());
							// std::cout << mk_pp(tail, m) << std::endl;
							break;
						}

					}
					new_tail[tail_idx] = tail;
					new_tail_neg[tail_idx] = rule->is_neg_tail(current_tail);
					++tail_idx;
				}

				for (unsigned j = rule->get_uninterpreted_tail_size(); j < rule->get_tail_size(); ++j) {
					app* tail = rule->get_tail(j);
					new_tail[tail_idx] = tail;
					new_tail_neg[tail_idx] = rule->is_neg_tail(j);
					++tail_idx;
				}

				rule_ref new_rule(rm);
				// std::cout << "make new rule" << std::endl;

				// new_rule = rm.mk(rule, new_head);

				new_rule = rm.mk(new_head, tail_idx,
					new_tail.c_ptr(), new_tail_neg.c_ptr(), rule->name(), false);

				// std::cout << "fix unbound" << std::endl;
				// rule->display(m_ctx, std::cout);
				// new_rule.get()->display(m_ctx, std::cout);
				// for (unsigned j = 0; j < new_rule.get()->get_tail_size(); ++j) {
				// 	std::cout << j << std::endl;
				// 	std::cout << mk_pp(new_rule.get()->get_tail(j)->get_decl(), m) << std::endl;
				// }
				rm.fix_unbound_vars(new_rule, false);
				// std::cout << "end" << std::endl;
				rules.replace_rule(rule, new_rule.get());
			}
		}
	}

    bool mk_mutual_recursion_eliminator::contains_one_of_functions_in_tail(rule & r, ptr_vector<func_decl> functions) {
		for (unsigned i = 0; i < r.get_uninterpreted_tail_size(); ++i) {
			if (functions.contains(r.get_tail(i)->get_decl())) {
				return true;
			}
		}
		return false;
    }

	void mk_mutual_recursion_eliminator::merge_mutual_in_tails(rule_set & rules, ptr_vector<func_decl> mutual_functions,
			obj_map<func_decl, unsigned> m_func2arg, func_decl * product_pred) {
		for (unsigned current_rule = 0; current_rule < rules.get_num_rules(); ++current_rule) {
			rule *rule = rules.get_rule(current_rule);
			if (contains_one_of_functions_in_tail(*rule, mutual_functions)) {
				ptr_vector<app> new_tail;
		        svector<bool> new_tail_neg;
		        new_tail.resize(rule->get_tail_size());
		        new_tail_neg.resize(rule->get_tail_size());
		        unsigned tail_idx = 0;
	            for (unsigned current_tail = 0; current_tail < rule->get_uninterpreted_tail_size(); ++current_tail) {
					app* tail = rule->get_tail(current_tail);
					for (unsigned n1 = 0; n1 < mutual_functions.size(); ++n1) {
						if (mutual_functions[n1] == tail->get_decl()) {
							unsigned args_num = product_pred->get_arity();
							ptr_vector<expr> args;
							args.resize(args_num);

							unsigned ind = 0;
							for (unsigned i = 0; i < n1; ++i) {
								for (unsigned j = 0; j < m_func2arg[mutual_functions[i]]; ++j) {
									args[ind] = m.mk_fresh_const("__av", product_pred->get_domain(ind));
									++ind;
								}
							}
							for (unsigned i = 0; i < m_func2arg[mutual_functions[n1]]; ++i) {
								args[ind] = tail->get_arg(i);
								++ind;
							}

							for (unsigned i = n1 + 1; i < mutual_functions.size(); ++i) {
								for (unsigned j = 0; j < m_func2arg[mutual_functions[i]]; ++j) {
									args[ind] = m.mk_fresh_const("__av", product_pred->get_domain(ind));
									++ind;
								}
							}
							args[ind] = m_autil.mk_int(n1);
							// std::cout << "new_tail" << std::endl;
							tail = m.mk_app(product_pred, args_num, args.c_ptr());
							// std::cout << mk_pp(tail, m) << std::endl;
							break;
						}
					}
					new_tail[tail_idx] = tail;
					new_tail_neg[tail_idx] = rule->is_neg_tail(current_tail);
					++tail_idx;
				}
				for (unsigned j = rule->get_uninterpreted_tail_size(); j < rule->get_tail_size(); ++j) {
					app* tail = rule->get_tail(j);
					new_tail[tail_idx] = tail;
					new_tail_neg[tail_idx] = rule->is_neg_tail(j);
					++tail_idx;
				}

				rule_ref new_rule(rm);
				// std::cout << "make new rule" << std::endl;
				new_rule = rm.mk(rule->get_head(), tail_idx,
				    new_tail.c_ptr(), new_tail_neg.c_ptr(), rule->name(), false);
				// std::cout << "fix unbound" << std::endl;
				// rule->display(m_ctx, std::cout);
				// new_rule.get()->display(m_ctx, std::cout);
				// for (unsigned j = 0; j < new_rule.get()->get_tail_size(); ++j) {
				// 	std::cout << j << std::endl;
				// 	std::cout << mk_pp(new_rule.get()->get_tail(j)->get_decl(), m) << std::endl;
				// }
				rm.fix_unbound_vars(new_rule, false);
				// std::cout << "end" << std::endl;
				rules.replace_rule(rule, new_rule.get());
				// std::cout << "replace" << std::endl;
			}
		}
	}

    void mk_mutual_recursion_eliminator::merge_mutual_recursion(rule_set & rules) {
		if (rules.close()) {
			rule_set::pred_set_vector const &strats = rules.get_strats();
	        for (unsigned i = 0; i < strats.size(); ++i) {
            	func_decl_set::iterator it = strats[i]->begin(), end = strats[i]->end();
            	func_decl * head;
            	bool is_mutual = false;
            	string_buffer<> buffer;
        		ptr_vector<sort> domain;
        		ptr_vector<func_decl> mutual_functions;
				obj_map<func_decl, unsigned> m_func2arg;
            	if (it != end) {
	                head = *it;
	                buffer << head->get_name();
	                domain.append(head->get_arity(), head->get_domain());
	                // std::cout << "head " << head->get_arity() << std::endl;
	                mutual_functions.push_back(head);
	                m_func2arg.insert(head, head->get_arity());
	            }
	            for (; it != end; ++it) {
	                func_decl* pred = *it;
	                if (pred != head) {
	                	is_mutual = true;
	                	buffer << "+";
	                	buffer << pred->get_name();
						domain.append(pred->get_arity(), pred->get_domain());
						// std::cout << pred->get_arity() << std::endl;
						// std::cout << "mutual" << std::endl;
						// std::cout << head->get_name() << std::endl;
						// std::cout << pred->get_name() << std::endl;
						mutual_functions.push_back(pred);
						m_func2arg.insert(pred, pred->get_arity());
					}
				}

				if (is_mutual) {
					symbol name = symbol(buffer.c_str());
					// std::cout << name << std::endl;
					// std::cout << domain.size() << std::endl;

					domain.push_back(m_autil.mk_int());
			        func_decl* product_pred = m_ctx.mk_fresh_head_predicate(name,
			        	symbol::null, domain.size(), domain.c_ptr(), head);
			        // std::cout << product_pred->get_name() << std::endl;

			        merge_mutual_in_heads(rules, mutual_functions, m_func2arg, product_pred);
			        // std::cout << "HEADS" << std::endl;
			        // rules.display(std::cout);
			        merge_mutual_in_tails(rules, mutual_functions, m_func2arg, product_pred);
			        // std::cout << "TAILS" << std::endl;
			        // rules.display(std::cout);
			    }
        	}
        }
        rules.reopen();
    }

    rule_set * mk_mutual_recursion_eliminator::operator()(rule_set const & source) {
		printf("\n\n----------------------------------\nMUTUAL RECURSION!\n");
		// printf("\n\n----------------------------------\nMUTUAL RECURSION! SOURCE RULES:\n");
		// source.display(std::cout);

        rule_set* rules = alloc(rule_set, m_ctx);
        rules->inherit_predicates(source);

        rule_set::iterator it = source.begin(), end = source.end();
        for (; it != end; ++it) {
            rules->add_rule(*it);
        }

        merge_mutual_recursion(*rules);
        printf("\n\n-----------------OUT OF MUTUAL:-----------------\n");

        // printf("\n\n-----------------RESULTING RULES:-----------------\n");
        // rules->display(std::cout);
        // printf("\n\n----------------------------------\n");
        return rules;
    }

};