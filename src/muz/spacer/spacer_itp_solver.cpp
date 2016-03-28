/** 
Spacer
Copyright (c) 2015 Carnegie Mellon University.
All Rights Reserved.

THIS SOFTWARE IS PROVIDED "AS IS," WITH NO WARRANTIES
WHATSOEVER. CARNEGIE MELLON UNIVERSITY EXPRESSLY DISCLAIMS TO THE
FULLEST EXTENT PERMITTEDBY LAW ALL EXPRESS, IMPLIED, AND STATUTORY
WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, AND
NON-INFRINGEMENT OF PROPRIETARY RIGHTS.

Released under a modified MIT license, please see SPACER_LICENSE.txt
for full terms.  DM-0002483

Spacer includes and/or makes use of the following Third-Party Software
subject to its own license:

Z3
Copyright (c) Microsoft Corporation
All rights reserved.

Released under the MIT License (LICENSE.txt)

Module Name:

    spacer_itp_solver.cpp

Abstract:

   A solver that produces interpolated unsat cores

Author:

    Arie Gurfinkel

Notes:
   
--*/
#include"spacer_itp_solver.h"
#include"ast.h"
#include"spacer_util.h"
#include"spacer_farkas_learner.h"
#include"expr_replacer.h"

namespace spacer
{
  void itp_solver::push ()
  {
    m_defs.push_back (def_manager (*this));
    m_solver.push ();
  }

  void itp_solver::pop (unsigned n)
  {
    m_solver.pop (n);
    unsigned lvl = m_defs.size ();
    SASSERT (n <= lvl);
    unsigned new_lvl = lvl-n;
    while (m_defs.size () > new_lvl)
    {
      m_num_proxies -= m_defs.back ().m_defs.size ();
      m_defs.pop_back ();
    }
  }
  
  app* itp_solver::fresh_proxy ()
  {
    if (m_num_proxies == m_proxies.size ())
    {
      std::stringstream name;
      name << "spacer_proxy!" << m_proxies.size ();
      app_ref res(m);
      res = m.mk_const (symbol (name.str ().c_str ()),
                        m.mk_bool_sort ());
      m_proxies.push_back (res);

      // -- add the new proxy to proxy eliminator
      proof_ref pr(m);
      pr = m.mk_asserted (m.mk_true ());
      m_elim_proxies_sub.insert (res, m.mk_true (), pr);
      
    }
    return m_proxies.get (m_num_proxies++);
  }
  
  app* itp_solver::mk_proxy (expr *v)
  {
    expr *e = v;
    m.is_not (e, e);
    if (is_uninterp_const (e)) return to_app(v);
    
    def_manager &def = m_defs.size () > 0 ? m_defs.back () : m_base_defs;
    return def.mk_proxy (e);
  }
  
  void itp_solver::mk_proxies (expr_ref_vector &v)
  {
    for (unsigned i = 0, sz = v.size (); i < sz; ++i)
      v[i] = mk_proxy (v.get (i));
  }
  
  lbool itp_solver::check_sat (unsigned num_assumptions, expr * const *assumptions)
  {
    m_assumptions.reset ();
    m_assumptions.append (num_assumptions, assumptions);
    spacer::expand_literals(m, m_assumptions);
    mk_proxies (m_assumptions);
    
    lbool res;
    res = m_solver.check_sat (m_assumptions.size (), m_assumptions.c_ptr ());
    set_status (res);
    
    return res;
  }
  
  app* itp_solver::def_manager::mk_proxy (expr *v)
  {
    app* r;
    if (m_expr2proxy.find (v, r)) return r;
    
    ast_manager &m = m_parent.m;
    app_ref proxy(m);
    app_ref def(m);
    proxy = m_parent.fresh_proxy ();
    def = m.mk_implies (proxy, v);
    m_defs.push_back (def);
    m_expr2proxy.insert (v, proxy);
    m_proxy2def.insert (proxy, def);
    
    m_parent.assert_expr (def.get ());
    return proxy;
  }
  
  bool itp_solver::def_manager::is_proxy (app *k, app_ref &def)
  {
    app *r = NULL;
    bool found = m_proxy2def.find (k, r);
    def = r;
    return found;
  }
  
  bool itp_solver::is_proxy(expr *e, app_ref &def)
  {
    if (!is_uninterp_const (e)) return false;
    
    app *a = to_app (e);

    for (int i = m_defs.size (); i > 0; --i)
      if (m_defs[i-1].is_proxy (a, def))
          return true;
        
    if (m_base_defs.is_proxy (a, def))
      return true;
    
    return false;
  }
  
  void itp_solver::get_unsat_core (ptr_vector<expr> &r)
  {
    m_solver.get_unsat_core (r);
    undo_proxies (r);
  }
  void itp_solver::undo_proxies (ptr_vector<expr> &r)
  {
    app_ref e(m);
    // expand proxies
    for (unsigned i = 0, sz = r.size (); i < sz; ++i)
      if (is_proxy (r[i], e))
      {
        SASSERT (m.is_implies (e));
        r[i] = e->get_arg (1);
      }
  }
  void itp_solver::undo_proxies (expr_ref_vector &r)
  {
    app_ref e(m);
    // expand proxies
    for (unsigned i = 0, sz = r.size (); i < sz; ++i)
      if (is_proxy (r.get (i), e))
      {
        SASSERT (m.is_implies (e));
        r[i] = e->get_arg (1);
      }
  }

  void itp_solver::get_unsat_core (expr_ref_vector &_core)
  {
    ptr_vector<expr> core;
    get_unsat_core (core);
    _core.append (core.size (), core.c_ptr ());
  }
  
  void itp_solver::elim_proxies (expr_ref_vector &v)
  {
    expr_ref f = mk_and (v);
    scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer (m);
    rep->set_substitution (&m_elim_proxies_sub);
    (*rep) (f);
    v.reset ();
    flatten_and (f, v);
  }
  
  void itp_solver::get_itp_core (expr_ref_vector &core)
  {
    
    // B side of the interpolant
    obj_hashtable<expr> B;
    for (unsigned i = 0, sz = m_assumptions.size (); i < sz; ++i)
    {
      expr *a = m_assumptions.get (i);
      app_ref def(m);
      if (is_proxy (a, def)) B.insert (def.get ());
      B.insert (a);
    }
    proof_ref pr(m);
    pr = get_proof ();
    farkas_learner farkas;
    farkas.set_split_literals (m_split_literals);
    
    core.reset ();
    farkas.get_lemmas (pr, B, core);
    elim_proxies (core);
    farkas.simplify_lemmas (core); // XXX potentially redundant

    IF_VERBOSE(2,
               verbose_stream () << "Itp Core:\n"
               << mk_pp (mk_and (core), m) << "\n";);
  }
  
  
}


