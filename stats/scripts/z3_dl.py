#!/usr/bin/env python

import z3
import sys
import stats

def parseArgs (argv):
    import argparse as a
    p = a.ArgumentParser (description='Z3 Datalog Frontend')
    
    p.add_argument ('file', metavar='BENCHMARK', help='Benchmark file')
    p.add_argument ('--pp', 
                    help='Enable default pre-processing', 
                    action='store_true', default=False)
    p.add_argument ('--validate', help='Enable validation',
                    action='store_true', default=False)
    p.add_argument ('--trace', help='Trace levels to enable (spacer, pdr, dl,'
                                    'smt-relation, etc.)', 
                    default='')
    p.add_argument ('--answer', help='Print answer', action='store_true',
                    default=False)
    p.add_argument ('--engine', help='Datalog Engine (pdr/spacer)', default='spacer')
    p.add_argument ('--verbose', help='Z3 verbosity', default=0)
    p.add_argument ('--use-utvpi', dest='use_utvpi', help='use utvpi/diff-logic '
                                                          'solvers, if applicable',
                    action='store_true', default=False)
    p.add_argument ('--eager-reach-check', dest='eager_reach_check',
                    help='eagerly use reachability facts for every local query',
                    action='store_true', default=False)
    p.add_argument ('--validate-theory-core', dest='validate_theory_core',
                    help='validate every theory core',
                    action='store_true', default=False)
    p.add_argument ('--from-lvl', dest='from_lvl',
                    type=int,
                    help='start level for query predicate',
                    action='store', default=0)
    p.add_argument ('--print-stats', dest='print_stats',
                    help='flag to print stats',
                    action='store_true', default=False)
    p.add_argument ('--dfs', dest='dfs',
                    help='use dfs instead of bfs',
                    action='store_true', default=False)
    p.add_argument ('--order-children', dest='order_children',
                    help='0 (rtol), 1 (ltor)', default=0)
    p.add_argument ('--use-qe-projection', dest='use_qe_projection',
                    help='use mbp (only for pdr)',
                    action='store_true', default=False)
    p.add_argument ('--bit-blast', dest='bit_blast',
                    help='blast bitvectors into bits',
                    action='store_true', default=False)
    p.add_argument ('--rule-stats', dest='rule_stats',
                    help='print rule statistics and exit',
                    action='store_true', default=False)

    return p.parse_args (argv)

def stat (key, val): stats.put (key, val)

def main (argv):
    args = parseArgs (argv[1:])
    stat ('Result', 'UNKNOWN')
    z3.set_option (verbose=args.verbose)
    ctx = z3.Context ()
    fp = z3.Fixedpoint (ctx=ctx)
    if not args.pp:
        print 'No pre-processing'
        fp.set (slice=False)
        fp.set (inline_linear=False)
        fp.set (inline_eager=False)

    print 'Engine: ', args.engine

    fp.set (validate_result=args.validate)
    fp.set (engine=args.engine, use_farkas=True, generate_proof_trace=False)
    fp.set (use_utvpi=args.use_utvpi)
    fp.set (eager_reach_check=args.eager_reach_check)
    fp.set (validate_theory_core=args.validate_theory_core)
    fp.set (print_statistics=args.print_stats)
    fp.set (bit_blast=args.bit_blast)

    if args.dfs: fp.set (bfs_model_search=False)

    fp.set (order_children=int(args.order_children))

    fp.set (use_qe_projection=args.use_qe_projection)

    fp.set (rule_stats=args.rule_stats)

    with stats.timer ('Parse'):
        q = fp.parse_file (args.file)

    if len(args.trace) > 0:
        print 'Enable trace: ',
        for t in args.trace.split (':'):
            print t,
            z3.enable_trace (t)
        print 
        stats.put ('Trace', args.trace)
    #print fp
    with stats.timer ('Query'):
        res = fp.query_from_lvl (args.from_lvl, q[0])

    if res == z3.sat: stat ('Result', 'CEX')
    elif res == z3.unsat: stat ('Result', 'SAFE')

    if args.answer:
        print 'The answer is:'
        print fp.get_answer ()
    
if __name__ == '__main__':
    try:
        res = main (sys.argv)
    finally:
        stats.brunch_print ()
    sys.exit (res)

