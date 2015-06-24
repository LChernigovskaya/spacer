/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    main.cpp

Abstract:

    Z3 command line tool.

Author:

    Leonardo de Moura (leonardo) 2006-10-10.
    Nikolaj Bjorner   (nbjorner) 

Adopted by:
    
    Derrick Karimi 2015-03-13

Revision History:

--*/
#include<iostream>
#include"trace.h"
#include"version.h"
#include"timeout.h"
#include"z3_exception.h"
#include"error_codes.h"
#include"gparams.h"
#include"env_params.h"
#include"z3_gasnet.h"
#include<sstream>
#ifdef Z3GASNET_PROFILING
#include"spacer_wall_stopwatch.h"
#endif
#include<vector>

#ifdef Z3GASNET
//Have to include in main  here for access to message handlers
#include "spacer_context.h"
#include <iostream>
#include <ostream>
#endif

extern "C" {
#include "z3.h"
}

#include "pmuz.h"
#include "pmuz_globals.h"


typedef enum { IN_UNSPECIFIED, IN_SMTLIB, IN_SMTLIB_2, IN_DATALOG, IN_DIMACS, IN_WCNF, IN_OPB, IN_Z3_LOG } input_kind;

std::string         g_aux_input_file;
char const *        g_input_file          = 0;
bool                g_standard_input      = false;
input_kind          g_input_kind          = IN_UNSPECIFIED;
bool                g_display_statistics  = false;
bool                g_display_istatistics = false;
std::string         g_profiles;
char const *        g_profile_names[] = { "def","gpdr","ic3", "Oc1def", "Oc1gpdr", "Oc1ic3" };
std::string         g_verbose_log_base;

void error(const char * msg) {
    std::cerr << "Error: " << msg << "\n";
    std::cerr << "For usage information: z3 -h\n";
    exit(ERR_CMD_LINE);
}

#define STRINGIZE(x) #x
#define STRINGIZE_VALUE_OF(x) STRINGIZE(x)

void display_usage() {
    std::cout << "Z3 [version " << Z3_MAJOR_VERSION << "." << Z3_MINOR_VERSION << "." << Z3_BUILD_NUMBER;
    std::cout << " - ";
#ifdef _AMD64_
    std::cout << "64";
#else
    std::cout << "32";
#endif
    std::cout << " bit";
#ifdef Z3GITHASH
    std::cout << " - build hashcode " << STRINGIZE_VALUE_OF(Z3GITHASH);
#endif
    std::cout << "]. (C) Copyright 2006-2014 Microsoft Corp, (C) Copyright 2015 Software Engineering Institute - Carnegie Mellon University.\n";
#ifdef Z3GASNET
    std::cout << "Usage: pmuz JOB_SIZE [options] [-file:]file\n";
#else
    std::cout << "Usage: pmuz [options] [-file:]file\n";
#endif
    std::cout << "\nInput format:\n";
    std::cout << "  -smt        use parser for SMT input format.\n";
    std::cout << "  -smt2       use parser for SMT 2 input format.\n";
    std::cout << "  -dl         use parser for Datalog input format.\n";
    std::cout << "  -dimacs     use parser for DIMACS input format.\n";
    std::cout << "  -log        use parser for Z3 log input format.\n";
    std::cout << "  -in         read formula from standard input.\n";
    std::cout << "\nMiscellaneous:\n";
    std::cout << "  -h, -?      prints this message.\n";
    std::cout << "  -version    prints version number of Z3.\n";
    std::cout << "  -v:level    be verbose, where <level> is the verbosity level.\n";
    std::cout << "  -vo:path    path to a file where verbose logging will be written\n";
    std::cout << "  -nw         disable warning messages.\n";
    std::cout << "  -p          display Z3 global (and module) parameters.\n";
    std::cout << "  -pd         display Z3 global (and module) parameter descriptions.\n";
    std::cout << "  -pm:name    display Z3 module ('name') parameters.\n";
    std::cout << "  -pp:name    display Z3 parameter description, if 'name' is not provided, then all module names are listed.\n";
#ifdef Z3GASNET
    std::cout << "  -profile:name0,name1,...    set predefined profiles of Z3 parameters.  If name list is provided its size should be N.  If no profile names are provided, a predefined set of profiles will be used.\n";
#else
    std::cout << "  -profile:name   set predefined profiles of Z3 parameters, if name is not provided 'def' will be used.\n";
#endif
    std::cout << "  --"      << "          all remaining arguments are assumed to be part of the input file name. This option allows Z3 to read files with strange names such as: -foo.smt2.\n";
    std::cout << "\nResources:\n";
    // timeout and memout are now available on Linux and OSX too.
    std::cout << "  -T:timeout  set the timeout (in seconds).\n";
    std::cout << "  -t:timeout  set the soft timeout (in milli seconds). It only kills the current query.\n";
    std::cout << "  -memory:Megabytes  set a limit for virtual memory consumption.\n";
    // 
    std::cout << "\nOutput:\n";
    std::cout << "  -st         display statistics.\n";
#if defined(Z3DEBUG) || defined(_TRACE)
    std::cout << "\nDebugging support:\n";
#endif
#ifdef _TRACE
    std::cout << "  -tr:tag     enable trace messages tagged with <tag>.\n";
#endif
#ifdef Z3DEBUG
    std::cout << "  -dbg:tag    enable assertions tagged with <tag>.\n";
#endif
    std::cout << "\nParameter setting:\n";
    std::cout << "Global and module parameters can be set in the command line.\n";
    std::cout << "  param_name=value              for setting global parameters.\n";
    std::cout << "  module_name.param_name=value  for setting module parameters.\n";
    std::cout << "Use 'z3 -p' for the complete list of global and module parameters.\n";
}
   
void parse_cmd_line_args(int argc, char ** argv) {
    int i = 1;
    char * eq_pos = 0;
    while (i < argc) {
        char * arg = argv[i];    

        if (arg[0] == '-' && arg[1] == '-' && arg[2] == 0) {
            // Little hack used to read files with strange names such as -foo.smt2
            // z3 -- -foo.smt2
            i++;
            g_aux_input_file = "";
            for (; i < argc; i++) {
                g_aux_input_file += argv[i];
                if (i < argc - 1)
                    g_aux_input_file += " ";
            }
            if (g_input_file) {
                warning_msg("input file was already specified.");
            }
            else {
                g_input_file = g_aux_input_file.c_str();
            }
            break;
        }
        
        if (arg[0] == '-' 
#ifdef _WINDOWS
            || arg[0] == '/'
#endif
            ) {
            char * opt_name = arg + 1;
            // allow names such as --help
            if (*opt_name == '-')
                opt_name++;
            char * opt_arg  = 0;
            char * colon    = strchr(arg, ':');
            if (colon) {
                opt_arg = colon + 1;
                *colon  = 0;
            }
            if (strcmp(opt_name, "h") == 0 || strcmp(opt_name, "?") == 0 || strcmp(opt_name, "help") == 0) {
                display_usage();
                exit(0);
            }
            if (strcmp(opt_name, "version") == 0) {
                std::cout << "Z3 version " << Z3_MAJOR_VERSION << "." << Z3_MINOR_VERSION << "." << Z3_BUILD_NUMBER << "\n";
                exit(0);
            }
            else if (strcmp(opt_name, "smt") == 0) {
                g_input_kind = IN_SMTLIB;
            }
            else if (strcmp(opt_name, "smt2") == 0) {
                g_input_kind = IN_SMTLIB_2;
            }
            else if (strcmp(opt_name, "in") == 0) {
                g_standard_input = true;
            }
            else if (strcmp(opt_name, "dimacs") == 0) {
                g_input_kind = IN_DIMACS;
            }
            else if (strcmp(opt_name, "wcnf") == 0) {
                g_input_kind = IN_WCNF;
            }
            else if (strcmp(opt_name, "bpo") == 0) {
                g_input_kind = IN_OPB;
            }
            else if (strcmp(opt_name, "log") == 0) {
                g_input_kind = IN_Z3_LOG;
            }
            else if (strcmp(opt_name, "st") == 0) {
                g_display_statistics = true; 
            }
            else if (strcmp(opt_name, "ist") == 0) {
                g_display_istatistics = true; 
            }
            else if (strcmp(opt_name, "v") == 0) {
                if (!opt_arg)
                    error("option argument (-v:level) is missing.");
                long lvl = strtol(opt_arg, 0, 10);
                set_verbosity_level(lvl);
            }
            else if (strcmp(opt_name, "file") == 0) {
                g_input_file = opt_arg;
            }
            else if (strcmp(opt_name, "T") == 0) {
                if (!opt_arg)
                    error("option argument (-T:timeout) is missing.");
                long tm = strtol(opt_arg, 0, 10);
                set_timeout(tm * 1000);
            }
            else if (strcmp(opt_name, "t") == 0) {
                if (!opt_arg)
                    error("option argument (-t:timeout) is missing.");
                Z3_global_param_set("timeout", opt_arg);
            }
            else if (strcmp(opt_name, "nw") == 0) {
                enable_warning_messages(false);
            }
            else if (strcmp(opt_name, "p") == 0) {
                gparams::display(std::cout, 0, false, false);
                exit(0);
            }
            else if (strcmp(opt_name, "pd") == 0) {
                gparams::display(std::cout, 0, false, true);
                exit(0);
            }
            else if (strcmp(opt_name, "pm") == 0) {
                if (opt_arg) {
                    gparams::display_module(std::cout, opt_arg);
                }
                else {
                    gparams::display_modules(std::cout);
                    std::cout << "\nUse -pm:name to display all parameters available at module 'name'\n";
                }
                exit(0);
            }
            else if (strcmp(opt_name, "pp") == 0) {
                if (!opt_arg)
                    error("option argument (-pp:name) is missing.");
                gparams::display_parameter(std::cout, opt_arg);
                exit(0);
            }
#ifdef _TRACE
            else if (strcmp(opt_name, "tr") == 0) {
                if (!opt_arg)
                    error("option argument (-tr:tag) is missing.");
                enable_trace(opt_arg);
            }
#endif
#ifdef Z3DEBUG
            else if (strcmp(opt_name, "dbg") == 0) {
                if (!opt_arg)
                    error("option argument (-dbg:tag) is missing.");
                enable_debug(opt_arg);
            }
#endif
            else if (strcmp(opt_name, "memory") == 0) {
                if (!opt_arg)
                    error("option argument (-memory:val) is missing.");
                Z3_global_param_set("memory_max_size", opt_arg);
            }
            else if (strcmp(opt_name, "profile") == 0) {
                g_profiles=!opt_arg ? "def" : opt_arg;
            }
            else if (strcmp(opt_name, "vo") == 0) {
                g_verbose_log_base=!opt_arg?"pmuz_verbose" : opt_arg;
            }
            else {
                std::cerr << "Error: invalid command line option: " << arg << "\n";
                std::cerr << "For usage information: z3 -h\n";
                exit(ERR_CMD_LINE);
            }
        }
        else if (argv[i][0] != '"' && (eq_pos = strchr(argv[i], '='))) {
            char * key   = argv[i];
            *eq_pos      = 0;
            char * value = eq_pos+1; 
            Z3_global_param_set(key, value);
        }
        else {
            if (g_input_file) {
                warning_msg("input file was already specified.");
            }
            else {
                g_input_file = arg;
            }
        }
        i++;
    }
}

char const * get_extension(char const * file_name) {
    if (file_name == 0)
        return 0;
    char const * last_dot = 0;
    for (;;) {
        char const * tmp = strchr(file_name, '.');
        if (tmp == 0) {
            return last_dot;
        }
        last_dot  = tmp + 1;
        file_name = last_dot;
    }
}

void profiles_string_to_vec(
    std::vector<std::string> &profile_vec,
    const std::string  &profiles_str)
{
  
  using namespace std;

  profile_vec.clear();
  size_t end = 0;
  size_t start = 0;
  const string delim(",");

  while ( end != string::npos)
  {
      end = profiles_str.find( delim, start);

      // If at end, use length=maxLength.  Else use length=end-start.
      profile_vec.push_back(profiles_str.substr( start,
                     (end == string::npos) ? string::npos : end - start));

      // If at end, use start=maxSize.  Else use start=end+delimiter.
      start = (   ( end > (string::npos - delim.size()) )
                ?  string::npos  :  end + delim.size());
  }
}

//stollen from
//http://stackoverflow.com/questions/874134/find-if-string-endswith-another-string-in-c
inline bool string_ends_with(std::string const & value, std::string const & ending)
{
    if (ending.size() > value.size()) return false;
    return std::equal(ending.rbegin(), ending.rend(), value.rbegin());
}

inline bool string_contains(std::string const & value, std::string const & substring)
{
    return value.find(substring) != std::string::npos;
}

void set_profile_params(const std::string &profile)
{
#ifdef Z3GASNET
  STRACE("gas", Z3GASNET_TRACE_PREFIX
      << "profile set to: " << profile << "\n";);
  size_t ms = std::string().max_size();

  STRACE("gas", Z3GASNET_TRACE_PREFIX
      << "System Info:\n\tgasnet_AMMaxMedium(): " << gasnet_AMMaxMedium() << "\n"
      << "\tgasnet_AMMaxLongRequest(): " << gasnet_AMMaxLongRequest() << "\n"
      << "\tgasnet_AMMaxLongReply(): " << gasnet_AMMaxLongReply() << "\n" 
      << "\tgasnet_getMaxLocalSegmentSize(): " << gasnet_getMaxLocalSegmentSize() << "\n" 
      << "\tsizeof(gasnet_handlerarg_t): " << sizeof(gasnet_handlerarg_t) << "\n" 
      << "\tsizeof(uintptr_t): " << sizeof(uintptr_t) << "\n" 
      << "\tsizeof(size_t): " << sizeof(size_t) << "\n" 
      << "\tsizeof(void*): " << sizeof(void*) << "\n" 
      << "\tstd::string::max_size(): " << ms << "\n" 
      ;);
#endif

  if (string_ends_with(profile,"def"))
  {
    //verbose_stream () << "BRUNCH_STAT distprofile def" << "\n";
    Z3_global_param_set("fixedpoint.use_heavy_mev","true");
    Z3_global_param_set("fixedpoint.reset_obligation_queue","false");
    Z3_global_param_set("fixedpoint.pdr.flexible_trace","true");
    Z3_global_param_set("fixedpoint.spacer.elim_aux","false");
    
  }
  else if (string_ends_with(profile,"ic3"))
  {
    //verbose_stream () << "BRUNCH_STAT distprofile ic3" << "\n";
    Z3_global_param_set("fixedpoint.use_heavy_mev","true");
    Z3_global_param_set("fixedpoint.pdr.flexible_trace","true");
    Z3_global_param_set("fixedpoint.spacer.elim_aux","false");
  }
  else if (string_ends_with(profile,"gpdr"))
  {
    //verbose_stream () << "BRUNCH_STAT distprofile gpdr" << "\n";
    Z3_global_param_set("fixedpoint.use_heavy_mev","true");
    Z3_global_param_set("fixedpoint.spacer.elim_aux","false");
  }
  else 
  {
    std::cerr << "Unrecognized profile: " << profile << std::endl;
    throw z3_error(ERR_CMD_LINE);
  }


  if (string_contains(profile,"Oc1"))
  {
    std::cout <<" ########## setting ordered childs\n" << std::endl;
    Z3_global_param_set("fixedpoint.order_children","1");
  }


}

void set_profile(std::vector<std::string> profile_vec)
{
  SASSERT(profile_vec.size() > 0);

#ifdef Z3GASNET

  //the user should have specified either 1 profile, or exactly 
  //number of nodes profiles
  size_t stock_profiles = sizeof(g_profile_names) / sizeof(char const *);

  // when parsing command line if profile was not explicitly
  // specified, it will be set as one "def".  Here we
  // detect defaults are desired and set available
  // profiles to the stock profiles
  if (profile_vec.size() == 1 && gasnet_nodes() > 1)
  {
    SASSERT(profile_vec[0] == "def");
    profile_vec.clear();
    for (size_t i = 0; i < stock_profiles && i < gasnet_nodes(); i++)
      profile_vec.push_back(g_profile_names[i]);
    SASSERT(profile_vec[0] == "def");
  }
  
  if (profile_vec.size() > gasnet_nodes())
  {
    std::cerr << "Either 0, 1 or " << std::min<size_t>(gasnet_nodes(),stock_profiles)
      << " profiles should be specified\n";
    throw z3_error(ERR_CMD_LINE);
  }

  set_profile_params(profile_vec[gasnet_mynode()]);

#else

  set_profile_params(profile_vec[0]);

#endif

}

unsigned core_main(bool &repeat, unsigned restarts)
{
  using namespace spacer;
  spacer::PMuz pmuz(g_input_file);
  pmuz.init();
  pmuz.createProblem();

  repeat = false; 
  //-- solve
#ifdef Z3GASNET

  std::stringstream msg;
  msg << "BRUNCH_STAT node_restarts " << restarts-1 << "\n";
  verbose_stream() << msg.str();

  unsigned budget = 1;
  SASSERT( restarts >= 0 );
  while(restarts--) budget *= 2;
  pmuz_globals::m_globals.m_cur_budget = budget;
  STRACE("gas", Z3GASNET_TRACE_PREFIX 
      << "Setting global budget to: " << budget << "\n";);
#endif

  Z3_lbool solution = pmuz.solve();
  if (solution == Z3_L_TRUE)
  {
    std::cout << "sat\n";
  }
  else if (solution == Z3_L_FALSE)
  {
    std::cout << "unsat\n";
  }
  else if (pmuz_globals::m_globals.m_spacer_context_restart) {
#ifdef Z3GASNET
    STRACE("gas", Z3GASNET_TRACE_PREFIX 
        << "Main is restarting pmuz node\n";);

    repeat = true;
#endif
  }
  else 
  {
        std::cout << "unknown\n";
  }

  unsigned return_value = Z3_get_error_code(pmuz.getZ3Context());
  pmuz.destroy();
  return return_value;
}



// borrowed from 
// http://forums.codeguru.com/showthread.php?460071-ostream-bit-bucket
class null_out_buf : public std::streambuf {
public:
    virtual std::streamsize xsputn ( const char * s, std::streamsize n ) { return n; }
};

class null_out_stream : public std::ostream {
public:
    null_out_stream() : std::ostream(&buf) {}
private:
   null_out_buf buf;
};


std::ostream &get_default_verbose_stream()
{
#ifdef Z3GASNET

  if (!g_verbose_log_base.size())
  {
      //In local spawning mode, it makes no sense to see mulitple verbose streams from
      //multiple processes because they are not synchronized
      //if not the master node 0, then set the null stream as default
      char *spawnfn = gasnet_getenv("GASNET_SPAWNFN");
      if (spawnfn && !strncmp("L",spawnfn,1) && gasnet_mynode()) 
      {
        static null_out_stream nullstream;
        return nullstream;
      }
  }
  else
  {
      std::vector<std::string> profile_vec;
      profiles_string_to_vec(profile_vec, g_profiles);

      std::stringstream nodelogfilename;
      nodelogfilename << g_verbose_log_base << ".node-" 
          << (int) gasnet_mynode() << ".profile-"
          << profile_vec[gasnet_mynode()] << ".verbose-"
          << (int) get_verbosity_level() << ".log";

      static std::ofstream verbose_file_stream(
              nodelogfilename.str().c_str());
      return verbose_file_stream;
  }
  return std::cerr;
#else
  if (!g_verbose_log_base.size())
  {
    return std::cerr;
  }
  else
  {
      std::stringstream nodelogfilename;
      nodelogfilename << g_verbose_log_base
          << ".verbose-" << (int) get_verbosity_level() 
          << ".log";

      static std::ofstream verbose_file_stream(
              nodelogfilename.str().c_str());
      return verbose_file_stream;
  }
#endif
}

#ifdef Z3GASNET

void print_exit_message(std::string exitcase, int exitcode)
{
    std::stringstream exitmsg;
    Z3GASNET_VERBOSE_STREAM(exitmsg, << " Exit case " << exitcase << " with code: " << exitcode << "\n");
    std::cout << exitmsg.str();
    std::cerr << exitmsg.str();
}

spacer::spacer_wall_stopwatch maintimer;

void stop_main_timer()
{
    maintimer.stop();
    std::stringstream maintimerstat;
    maintimerstat << "BRUNCH_STAT main_time "
        << maintimer.get_seconds() << "\n";
    verbose_stream() << maintimerstat.str();

}
//chained signal hanlder code stolen from
//http://stackoverflow.com/questions/17102919/it-is-valid-to-have-multiple-signal-handlers-for-same-signal

typedef struct sigaction sigaction_t;

static void (*gasnet_sigquit_handler)(int) = NULL;

static void pmuz_sigquit_handler(int signum)
{
    //gasnet does provide a default sigquit handler, see gasnet_internal.c
    //the default sigquit handler just calls gasnet_exit(1) in case the user
    //did not set a quit hanlder.  So even though we went through the trouble
    //of getting a pointer to the old hanlder, we won't call it
    if (gasnet_sigquit_handler){
        //gasnet_sigquit_handler(signum);
    }
    print_exit_message("SIGQUIT_HANDLER",123);
    stop_main_timer();
    gasnet_exit(123);
}

//custom handler is for testing use kill -50 to trigger it
static void (*gasnet_sigcustom_handler)(int) = NULL;

static void pmuz_sigcustom_handler(int signum)
{
    Z3GASNET_VERBOSE_STREAM( std::cout, << "Got custom signal " << signum << "\n");
    gasnett_print_backtrace_ifenabled(0);
    if (gasnet_sigcustom_handler) gasnet_sigcustom_handler(signum);
}

void set_signal_handlers()
{
    // in general, we don't want to overwrite any signal handlers gasnet uses
    // in the case of SIGQUIT, we could because it is designed to be set by
    // the user to do application shutdown in the case that some node in the
    // job has called gasnet_exit
    
    sigaction_t gasnet_handler;
    sigaction(SIGQUIT, NULL, &gasnet_handler);
    gasnet_sigquit_handler = gasnet_handler.sa_handler;
    sigaction_t pmuz_handler;
    memset(&pmuz_handler, 0, sizeof(pmuz_handler));
    pmuz_handler.sa_handler = pmuz_sigquit_handler;
    sigemptyset(&pmuz_handler.sa_mask);
    sigaction(SIGQUIT, &pmuz_handler, NULL);


    //randomly chose signal 50 for use for testing, this should be 
    //removed after constuction is complete

#define SIGCUSTOM 50
    sigaction(SIGCUSTOM, NULL, &gasnet_handler);
    gasnet_sigcustom_handler = gasnet_handler.sa_handler;
    memset(&pmuz_handler, 0, sizeof(pmuz_handler));
    pmuz_handler.sa_handler = pmuz_sigcustom_handler;
    sigemptyset(&pmuz_handler.sa_mask);
    sigaction(SIGCUSTOM, &pmuz_handler, NULL);
}

#endif


int main(int argc, char ** argv) {
    unsigned return_value = 19;

    try{
        maintimer.start();

        //memory::initialize(0);
        //memory::exit_when_out_of_memory(true, "ERROR: out of memory");

#ifdef Z3GASNET

        //Register the messange handlers 
        z3gasnet::context::register_queue_msg_handlers();

        // gasnet places itself in front of any applicaiton cmdline handling
        // it will strip off the arguments it uses inside gasnet_init and 
        // the returned state of argc, argv can be used as normal by the the app
        Z3GASNET_CHECKCALL(gasnet_init(&argc, &argv));


        // gasnet will block here until all nodes of the job are attached
        Z3GASNET_CHECKCALL(gasnet_attach(
              z3gasnet::get_handler_table(),
              z3gasnet::get_num_handler_table_entires(),
              gasnet_getMaxLocalSegmentSize(),0));

        set_signal_handlers();

        z3gasnet::context::set_seginfo_table();



#endif

        parse_cmd_line_args(argc, argv);
        
        //control verbose output, so we can avoid forked processes outputting
        //to the same stream
        set_verbose_stream(get_default_verbose_stream());

        if (g_profiles.size())
        {
          std::vector<std::string> profile_vec;
          profiles_string_to_vec(profile_vec, g_profiles);
          set_profile(profile_vec);
        }

        env_params::updt_params();

        bool repeat = false;
        unsigned restarts = 0;
        do { return_value = core_main(repeat,restarts++); } while (repeat);


#ifdef Z3GASNET
        STRACE("gas", Z3GASNET_TRACE_PREFIX 
            << "exit\n";);
        /*
        spacer::spacer_wall_stopwatch exittimer;
        exittimer.start();

        gasnet_barrier_notify(0,0);
        Z3GASNET_CHECKCALL(gasnet_barrier_wait(0,0));

        exittimer.stop();

        STRACE("gas", Z3GASNET_TRACE_PREFIX 
            << "Exiting after " << exittimer.get_seconds() << "\n";);

        */

        //use a temporary string stream to assemble the message, this helps prevent
        //interleaved stdout/stderr on forked processes

        print_exit_message("END_OF_MAIN",return_value);

        gasnet_exit(return_value);
#endif
    }
    catch (z3_exception & ex) {
        // unhandled exception

        std::cerr << "ERROR: " << ex.msg() << "\n";
        if (ex.has_error_code()) {
            return_value = ex.error_code();
#ifdef Z3GASNET
            print_exit_message("Z3_EXCEPTION_WITH_EC",return_value);
            gasnet_exit(return_value);
#endif
        }
        else {
            return_value = ERR_INTERNAL_FATAL;
#ifdef Z3GASNET
            print_exit_message("Z3_EXCEPTION",return_value);
            gasnet_exit(return_value);
#endif
        }
    }

    stop_main_timer();

    return return_value;
}

