 
 
"Vim SystemVerilog Syntax Highlight
"-------------------------------------------------------------------------------------
" Vim syntax file
" Language:     Verilog/SystemVerilog HDL + UVM
" Author:       Amit Sethi, Amal Khailtash, Khalid Siddiqi
" Last Change:  Sun Mar  6 21:11:18 PST 2011
" Version:      3.0
"
" Maintainer:
"
" Authors:
"   Amit Sethi     <amitrajsethi@yahoo.com>
"   Amal Khailtash <akhailtash@rogers.com>
"   Khalid Siddiqi <khalid2@yahoo.com>
"
" Credits:
"   Originally created by
"     Amit Sethi <amitrajsethi@yahoo.com>
"   OVM 2.0 Classes/Methods
"     Amal Khailtash <akhailtash@rogers.com>
"   OVM 2.0 to UVM conversion
"     Khalid Siddiqi <khalid2@yahoo.com>
"
" Revision Comments:
"     Amit Sethi <amitrajsethi@yahoo.com> - Thu Jul 27 12:54:08 IST 2006
"       Version 1.1
"     Amal Khailtash <akhailtash@rogers.com> - Mon Sep 29 09:55:42 EDT 2008
"       Version 2.0
"       Added OVM 2.0 Keyworks
"       Another option is the work by Anil Raj Gopalakrishnan <anilraj.gr@gmail.com>
"         http://verifideas.blogspot.com/2008/09/better-syntax-highlighting-in.html
"     Khalid Siddiqi <khalid2@yahoo.com> Sun Mar  6 21:11:18 PST 2011
"       Version 3.0
"       Converted OVM 2.0 version to UVM
" Extends Verilog syntax
" Requires $VIMRUNTIME/syntax/verilog.vim to exist
" For more info on setting $VIMRUNTIME etc. see:
" http://vimdoc.sourceforge.net/htmldoc/syntax.html
" For version 5.x: Clear all syntax items
" For version 6.x: Quit when a syntax file was already loaded
"-------------------------------------------------------------------------------------
if version < 600
   syntax clear
elseif exists("b:current_syntax")
   finish
endif
" Read in Verilog syntax files
if version < 600
   so syntax/verilog.vim
else
   runtime! syntax/verilog.vim
endif
syn sync lines=1000
"##########################################################
"       SystemVerilog Syntax
"##########################################################
syn keyword verilogStatement   module endmodule
syn keyword verilogStatement   always_comb always_ff always_latch
syn keyword verilogStatement   class endclass
syn keyword verilogStatement   virtual local const protected
syn keyword verilogStatement   package endpackage
syn keyword verilogStatement   rand randc constraint randomize
syn keyword verilogStatement   with inside dist
syn keyword verilogStatement   randcase
syn keyword verilogStatement   sequence endsequence randsequence
syn keyword verilogStatement   get_randstate set_randstate
syn keyword verilogStatement   srandom
syn keyword verilogStatement   logic bit byte time
syn keyword verilogStatement   int longint shortint
syn keyword verilogStatement   struct packed
syn keyword verilogStatement   final
syn keyword verilogStatement   import export
syn keyword verilogStatement   context pure
syn keyword verilogStatement   void shortreal chandle string
syn keyword verilogStatement   clocking endclocking
syn keyword verilogStatement   interface endinterface modport
syn keyword verilogStatement   cover covergroup coverpoint endgroup
syn keyword verilogStatement   property endproperty
syn keyword verilogStatement   program endprogram
syn keyword verilogStatement   bins binsof illegal_bins ignore_bins
syn keyword verilogStatement   alias matches solve static assert
syn keyword verilogStatement   assume super before expect bind
syn keyword verilogStatement   extends null tagged extern this implements
syn keyword verilogStatement   first_match throughout timeprecision
syn keyword verilogStatement   timeunit priority type union unique
syn keyword verilogStatement   uwire var cross ref wait_order intersect
syn keyword verilogStatement   wildcard within
syn keyword verilogStatement   semaphore triggered
syn keyword verilogStatement   std
syn keyword verilogStatement   new
syn keyword verilogTypeDef     typedef enum
syn keyword verilogConditional iff
syn keyword verilogRepeat      return break continue
syn keyword verilogRepeat      do while foreach
syn keyword verilogLabel       join_any join_none forkjoin
syn match   verilogGlobal      "`begin_\w\+"
syn match   verilogGlobal      "`end_\w\+"
syn match   verilogGlobal      "`remove_\w\+"
syn match   verilogGlobal      "`restore_\w\+"
syn match   verilogGlobal      "`[a-zA-Z0-9_]\+\>"
syn match   verilogNumber      "\<[0-9][0-9_\.]\=\([fpnum]\|\)s\>"
syn match   verilogNumber      "\<[0-9][0-9_\.]\=step\>"
syn match   verilogMethod      "\.atobin\>"
syn match   verilogMethod      "\.atohex\>"
syn match   verilogMethod      "\.atoi\>"
syn match   verilogMethod      "\.atooct\>"
syn match   verilogMethod      "\.atoreal\>"
syn match   verilogMethod      "\.await\>"
syn match   verilogMethod      "\.back\>"
syn match   verilogMethod      "\.bintoa\>"
syn match   verilogMethod      "\.clear\>"
syn match   verilogMethod      "\.compare\>"
syn match   verilogMethod      "\.data\>"
syn match   verilogMethod      "\.delete\>"
syn match   verilogMethod      "\.empty\>"
syn match   verilogMethod      "\.eq\>"
syn match   verilogMethod      "\.erase\>"
syn match   verilogMethod      "\.erase_range\>"
syn match   verilogMethod      "\.exists\>"
syn match   verilogMethod      "\.find\>"
syn match   verilogMethod      "\.find_first\>"
syn match   verilogMethod      "\.find_first_index\>"
syn match   verilogMethod      "\.find_index\>"
syn match   verilogMethod      "\.find_last\>"
syn match   verilogMethod      "\.find_last_index\>"
syn match   verilogMethod      "\.finish\>"
syn match   verilogMethod      "\.first\>"
syn match   verilogMethod      "\.front\>"
syn match   verilogMethod      "\.get\>"
syn match   verilogMethod      "\.getc\>"
syn match   verilogMethod      "\.hextoa\>"
syn match   verilogMethod      "\.icompare\>"
syn match   verilogMethod      "\.index\>"
syn match   verilogMethod      "\.insert\>"
syn match   verilogMethod      "\.insert_range\>"
syn match   verilogMethod      "\.itoa\>"
syn match   verilogMethod      "\.kill\>"
syn match   verilogMethod      "\.last\>"
syn match   verilogMethod      "\.len\>"
syn match   verilogMethod      "\.max\>"
syn match   verilogMethod      "\.min\>"
syn match   verilogMethod      "\.name\>"
syn match   verilogMethod      "\.neq\>"
syn match   verilogMethod      "\.new\>"
syn match   verilogMethod      "\.next\>"
syn match   verilogMethod      "\.num\>"
syn match   verilogMethod      "\.octtoa\>"
syn match   verilogMethod      "\.peek\>"
syn match   verilogMethod      "\.pop_back\>"
syn match   verilogMethod      "\.pop_front\>"
syn match   verilogMethod      "\.prev\>"
syn match   verilogMethod      "\.product\>"
syn match   verilogMethod      "\.purge\>"
syn match   verilogMethod      "\.push_back\>"
syn match   verilogMethod      "\.push_front\>"
syn match   verilogMethod      "\.put\>"
syn match   verilogMethod      "\.putc\>"
syn match   verilogMethod      "\.rand_mode\>"
syn match   verilogMethod      "\.constraint_mode\>"
syn match   verilogMethod      "\.realtoa\>"
syn match   verilogMethod      "\.resume\>"
syn match   verilogMethod      "\.reverse\>"
syn match   verilogMethod      "\.rsort\>"
syn match   verilogMethod      "\.self\>"
syn match   verilogMethod      "\.set\>"
syn match   verilogMethod      "\.shuffle\>"
syn match   verilogMethod      "\.size\>"
syn match   verilogMethod      "\.sort\>"
syn match   verilogMethod      "\.start\>"
syn match   verilogMethod      "\.status\>"
syn match   verilogMethod      "\.stop\>"
syn match   verilogMethod      "\.substr\>"
syn match   verilogMethod      "\.sum\>"
syn match   verilogMethod      "\.suspend\>"
syn match   verilogMethod      "\.swap\>"
syn match   verilogMethod      "\.tolower\>"
syn match   verilogMethod      "\.toupper\>"
syn match   verilogMethod      "\.try_get\>"
syn match   verilogMethod      "\.try_peek\>"
syn match   verilogMethod      "\.try_put\>"
syn match   verilogMethod      "\.unique\>"
syn match   verilogMethod      "\.unique_index\>"
syn match   verilogMethod      "\.xor\>"
syn match   verilogAssertion   "\<\w\+\>\s*:\s*\<assert\>\_.\{-});"
"-------------------------------------------------------------------------------
" UVM
"syn match   uvmClass           "\<uvm_\w\+\>"
"syn match   uvmClass           "\<uvm_tlm_\w\+\>"
"syn keyword uvmClass            
"syn keyword uvmMethod           
"syn keyword uvmMethodGlobal     
"syn keyword uvmDeprecatedMethod 
"-------------------------------------------------------------------------------
" uvm_sv/src/base/
"-------------------------------------------------------------------------------
" uvm_sv/src/base/uvm_component.svh
syn keyword uvmClass             uvm_component
syn keyword uvmMethod            accept_tr apply_config_settings begin_child_tr begin_tr build check clone
syn keyword uvmMethod            connect create create_component create_object do_accept_tr do_begin_tr do_end_tr
syn keyword uvmMethod            do_flush do_func_phase do_kill_all do_resolve_bindings do_task_phase end_of_elaboration
syn keyword uvmMethod            end_tr extract flush get_child get_config_int get_config_object get_config_string
syn keyword uvmMethod            get_first_child get_full_name get_next_child get_num_children get_parent has_child
syn keyword uvmMethod            kill lookup m_begin_tr print_config_settings print_override_info record_error_tr
syn keyword uvmMethod            record_event_tr report resolve_bindings restart resume run set_config_int set_config_object
syn keyword uvmMethod            set_config_string set_inst_override set_inst_override_by_type set_name
syn keyword uvmMethod            set_report_default_file_hier set_report_id_action_hier set_report_id_file_hier set_report_id_verbosity
syn keyword uvmMethod            set_report_severity_action_hier set_report_severity_file_hier
syn keyword uvmMethod            set_report_severity_id_action_hier set_report_severity_id_file_hier
syn keyword uvmMethod            set_report_verbosity_level_hier set_type_override set_type_override_by_type
syn keyword uvmMethod            start_of_simulation status stop suspend
syn keyword uvmDeprecatedMethod  configure export_connections find_component find_components get_component
syn keyword uvmDeprecatedMethod  get_num_components
"syn keyword uvmDeprecatedMethod  global_stop_request
syn keyword uvmDeprecatedMethod  import_connections post_new pre_run
syn keyword uvmDeprecatedClass   uvm_threaded_component
" uvm_sv/src/base/uvm_config.svh
syn keyword uvmClass             uvm_config_setting
syn keyword uvmMethod            matches_string print_match type_string value_string
syn keyword uvmClass             uvm_int_config_setting
syn keyword uvmMethod            matches_string type_string value_string
syn keyword uvmClass             uvm_string_config_setting
syn keyword uvmMethod            matches_string type_string value_string
syn keyword uvmClass             uvm_object_config_setting
syn keyword uvmMethod            matches_string type_string value_string
syn keyword uvmMethodGlobal      set_config_int set_config_object set_config_string
" uvm_sv/src/base/uvm_env.svh
syn keyword uvmClass             uvm_env
syn keyword uvmMethod            do_task_phase get_type_name run_test
syn keyword uvmDeprecatedMethod  do_test
" uvm_sv/src/base/uvm_event.svh
syn keyword uvmClass             uvm_event_callback
syn keyword uvmMethod            create pre_trigger post_trigger
syn keyword uvmClass             uvm_event
syn keyword uvmMethod            add_callback cancel create delete_callback do_copy do_print get_num_waiters
syn keyword uvmMethod            get_trigger_data get_trigger_time get_type_name is_off is_on reset trigger
syn keyword uvmMethod            wait_off wait_on wait_ptrigger wait_ptrigger_data wait_trigger wait_trigger_data
syn keyword uvmClass             uvm_event_pool
syn keyword uvmMethod            create delete do_copy do_print exists first get get_global_pool get_type_name
syn keyword uvmMethod            last next num prev
syn keyword uvmClass             uvm_barrier
syn keyword uvmMethod            cancel create do_copy do_print get_num_waiters get_threshold get_type_name
syn keyword uvmMethod            reached_threshold reset set_auto_reset set_threshold wait_for
syn keyword uvmClass             uvm_barrier_pool
syn keyword uvmMethod            create delete do_copy do_print exists first get get_global_pool get_type_name
syn keyword uvmMethod            last next num prev
" uvm_sv/src/base/uvm_report_server.svh
syn keyword uvmClass             uvm_report_server
syn keyword uvmMethod            compose_message copy_id_counts copy_severity_counts dump_server_state
syn keyword uvmMethod            f_display get_id_count get_max_quit_count get_quit_count get_severity_count
syn keyword uvmMethod            incr_id_count incr_quit_count incr_severity_count is_quit_count_reached
syn keyword uvmMethod            process_report report reset_quit_count reset_severity_counts set_id_count
syn keyword uvmMethod            set_max_quit_count set_quit_count set_severity_count summarize
syn keyword uvmClass             uvm_report_global_server
syn keyword uvmMethod            get_server set_server
" uvm_sv/src/base/uvm_factory.svh
syn keyword uvmClass             uvm_object_wrapper
syn keyword uvmMethod            create_component create_object get_type_name
syn keyword uvmClass             uvm_factory_override
syn keyword uvmClass             uvm_factory
syn keyword uvmMethod            create_component_by_name create_component_by_type create_object_by_name
syn keyword uvmMethod            create_object_by_type debug_create_by_name debug_create_by_type
syn keyword uvmMethod            find_override_by_name find_override_by_type sprint print register set_inst_override_by_name
syn keyword uvmMethod            set_inst_override_by_type set_type_override_by_name set_type_override_by_type
syn keyword uvmDeprecatedMethod  auto_register
"syn keyword uvmDeprecatedMethod  create_component create_object
syn keyword uvmDeprecatedMethod  print_all_overrides
"syn keyword uvmDeprecatedMethod  print_override_info set_inst_override set_type_override
" uvm_sv/src/base/uvm_misc.svh
syn keyword uvmCompatibility     avm_virtual_class
syn keyword uvmClass             uvm_void
syn keyword uvmClass             uvm_scope_stack
syn keyword uvmMethod            current depth down down_element get get_arg in_hierarchy set
syn keyword uvmMethod            set_arg set_arg_element unset_arg up up_element
syn keyword uvmMethodGlobal      uvm_bits_to_string uvm_is_match uvm_string_to_bits uvm_wait_for_nba_region
" uvm_sv/src/base/uvm_object.svh
syn keyword uvmClass             uvm_status_container
syn keyword uvmMethod            get_full_scope_arg init_scope
syn keyword uvmClass             uvm_object
syn keyword uvmMethod            clone compare copy create do_compare do_copy do_pack do_print do_record
syn keyword uvmMethod            do_sprint do_unpack get_full_name get_inst_count get_inst_id get_name
syn keyword uvmMethod            get_type get_type_name pack pack_bytes pack_ints print_field_match record
syn keyword uvmMethod            set_int_local set_name set_object_local set_string_local unpack unpack_bytes unpack_ints
syn keyword uvmClass             uvm_copy_map
syn keyword uvmMethod            clear delete get set
syn keyword uvmClass             uvm_comparer
syn keyword uvmMethod            compare_field compare_field_int compare_object compare_string init
syn keyword uvmMethod            print_msg print_msg_object print_rollup
syn keyword uvmClass             uvm_recorder
syn keyword uvmMethod            record_field record_generic record_object record_string record_time
syn keyword uvmClass             uvm_options_container
syn keyword uvmMethod            init
" uvm_sv/src/base/uvm_object_globals.svh
syn keyword uvmTypeDef           uvm_bitstream_t uvm_radix_enum uvm_recursion_policy_enum
" uvm_sv/src/base/uvm_packer
syn keyword uvmClass             uvm_packer
syn keyword uvmMethod            enough_bits get_bit get_bits get_byte get_bytes get_int get_ints get_packed_bits
syn keyword uvmMethod            get_packed_size index_error is_null pack_field pack_field_int pack_object
syn keyword uvmMethod            pack_real pack_string pack_time put_bits put_bytes put_ints reset set_packed_size
syn keyword uvmMethod            unpack_field unpack_field_int unpack_object unpack_object_ext unpack_real
syn keyword uvmMethod            unpack_string unpack_time
" uvm_sv/src/base/uvm_port_base.svh
syn keyword uvmTypeDef           uvm_port_type_e uvm_port_list
syn keyword uvmClass             uvm_port_component_base
syn keyword uvmMethod            get_connected_to get_provided_to is_export is_imp is_port
syn keyword uvmClass             uvm_port_component
syn keyword uvmMethod            do_display get_connected_to get_port get_provided_to get_type_name is_port is_export
syn keyword uvmMethod            is_imp resolve_bindings
syn keyword uvmClass             uvm_port_base
syn keyword uvmMethod            connect debug_connected_to debug_provided_to get_comp get_connected_to get_full_name
syn keyword uvmMethod            get_if get_name get_parent get_provided_to get_type_name is_export is_imp is_port
syn keyword uvmMethod            is_unbounded max_size min_size resolve_bindings set_default_index set_if size
"syn keyword uvmDeprecatedMethod  do_display remove
syn keyword uvmDeprecatedMethod  check_min_connection_size  lookup_indexed_if
" uvm_sv/src/base/uvm_printer.svh
syn keyword uvmClass             uvm_printer_knobs
syn keyword uvmMethod            get_radix_str
syn keyword uvmClass             uvm_printer
syn keyword uvmMethod            indent index index_string istop print_array_footer print_array_header
syn keyword uvmMethod            print_array_range print_field print_footer print_generic print_header
syn keyword uvmMethod            print_id print_newline print_object print_object_header print_size
syn keyword uvmMethod            print_string print_time print_type_name print_value print_value_array
syn keyword uvmMethod            print_value_object print_value_string write_stream
syn keyword uvmClass             uvm_hier_printer_knobs
syn keyword uvmClass             uvm_table_printer_knobs
syn keyword uvmClass             uvm_table_printer
syn keyword uvmMethod            print_footer print_header print_id print_size print_type_name print_value
syn keyword uvmMethod            print_value_array print_value_object print_value_string
syn keyword uvmClass             uvm_tree_printer_knobs
syn keyword uvmClass             uvm_tree_printer
syn keyword uvmMethod            print_array_footer print_id print_object print_object_header print_scope_close
syn keyword uvmMethod            print_scope_open print_string print_type_name print_value_array print_value_object
syn keyword uvmClass             uvm_line_printer
syn keyword uvmMethod            print_newline
" uvm_sv/src/base/uvm_registry.svh
syn keyword uvmClass             uvm_component_registry
syn keyword uvmMethod            create create_component get get_type_name set_inst_override set_type_override
syn keyword uvmClass             uvm_object_registry
syn keyword uvmMethod            create create_object get get_type_name set_type_override
" uvm_sv/src/base/uvm_report_defines.svh
syn keyword uvmTypeDef           uvm_action uvm_action_type uvm_severity uvm_severity_type uvm_verbosity
syn keyword uvmTypeDef           id_actions_array id_file_array uvm_FILE s_default_action_array s_default_file_array
" uvm_sv/src/base/uvm_report_global.svh
syn keyword uvmMethodGlobal      uvm_get_max_verbosity uvm_initialize_global_reporter uvm_report_error
syn keyword uvmMethodGlobal      uvm_report_fatal uvm_report_info uvm_report_warning
" uvm_sv/src/base/uvm_report_handler.svh
syn keyword uvmClass             uvm_hash
syn keyword uvmMethod            exists fetch first get next set
syn keyword uvmClass             uvm_report_handler
syn keyword uvmMethod            dump_state format_action get_action get_file_handle get_server get_verbosity_level
syn keyword uvmMethod            initialize report report_header run_hooks set_default_file set_defaults
syn keyword uvmMethod            set_id_action set_id_file set_max_quit_count set_severity_action set_severity_file
syn keyword uvmMethod            set_severity_id_action set_severity_id_file set_verbosity_level summarize
syn keyword uvmClass             default_report_server
syn keyword uvmMethod            get_server
" uvm_sv/src/base/uvm_report_object.svh
syn keyword uvmClass             uvm_report_object
syn keyword uvmMethod            die dump_report_state get_report_handler get_report_server uvm_get_max_verbosity
syn keyword uvmMethod            uvm_report_error uvm_report_fatal uvm_report_info uvm_report_warning
syn keyword uvmMethod            report_error_hook report_fatal_hook report_header report_hook report_info_hook
syn keyword uvmMethod            report_summarize report_warning_hook reset_report_handler set_report_default_file
syn keyword uvmMethod            set_report_handler set_report_id_action set_report_id_file set_report_max_quit_count
syn keyword uvmMethod            set_report_severity_action set_report_severity_file set_report_severity_id_action
syn keyword uvmMethod            set_report_severity_id_file set_report_verbosity_level
"syn keyword uvmDeprecatedMethod  avm_report_error avm_report_fatal avm_report_message avm_report_warning
syn keyword uvmClass             uvm_reporter
syn keyword uvmMethod            create get_type_name
" uvm_sv/src/base/uvm_report_server.svh
syn keyword uvmClass             uvm_report_server
syn keyword uvmMethod            compose_message copy_id_counts copy_severity_counts dump_server_state
syn keyword uvmMethod            f_display get_id_count get_max_quit_count get_quit_count get_severity_count
syn keyword uvmMethod            incr_id_count incr_quit_count incr_severity_count is_quit_count_reached
syn keyword uvmMethod            process_report report reset_quit_count reset_severity_counts set_id_count
syn keyword uvmMethod            set_max_quit_count set_quit_count set_severity_count summarize
syn keyword uvmClass             uvm_report_global_server
syn keyword uvmMethod            get_server set_server
" uvm_sv/src/base/uvm_root.svh
syn keyword uvmClass             uvm_root
syn keyword uvmMethod            find find_all get get_current_phase get_phase_by_name get_type_name
syn keyword uvmMethod            insert_phase run_global_phase run_test stop_request
syn keyword uvmDeprecatedClass   uvm_test_top
syn keyword uvmDeprecatedMethod  print_topology print_unit print_unit_list print_units
syn keyword uvmMethodGlobal      global_stop_request uvm_find_component uvm_print_topology run_test
syn keyword uvmMethodGlobal      set_global_stop_timeout set_global_timeout
" uvm_sv/src/base/uvm_transaction.svh
syn keyword uvmClass             uvm_transaction
syn keyword uvmMethod            accept_tr begin_child_tr begin_tr convert2string disable_recording
syn keyword uvmMethod            do_accept_tr do_begin_tr do_copy do_end_tr do_print do_record
syn keyword uvmMethod            enable_recording end_tr get_accept_time get_begin_time get_end_time
syn keyword uvmMethod            get_event_pool get_initiator get_tr_handle get_transaction_id is_active
syn keyword uvmMethod            is_recording_enabled m_begin_tr set_initiator set_transaction_id
" uvm_sv/src/base/uvm_version.svh
syn keyword uvmMethodGlobal      uvm_revision_string
"-------------------------------------------------------------------------------
" uvm_sv/src/base/compatibility/
"-------------------------------------------------------------------------------
" uvm_sv/src/base/compatibility/avm_compatibility.svh
syn keyword uvmCompatibility     avm_env avm_named_component avm_report_client avm_report_handler
syn keyword uvmCompatibility     avm_report_server avm_reporter avm_threaded_component avm_transaction
syn keyword uvmCompatibility     action action_type severity
syn keyword uvmCompatibility     uvm_named_component uvm_report_client
syn keyword uvmCompatibility     avm_transport_port avm_transport_export avm_built_in_pair
syn keyword uvmCompatibility     avm_class_pair avm_in_order_comparator avm_in_order_class_comparator
syn keyword uvmCompatibility     avm_in_order_built_in_comparator avm_algorithmic_comparator
syn keyword uvmCompatibility     avm_report_error avm_report_fatal avm_report_message avm_report_warning
syn keyword uvmCompatibility     analysis_fifo avm_transport_imp avm_analysis_imp avm_port_base
" uvm_sv/src/base/compatibility/base_compatibility.svh
"syn keyword uvmClass            
"syn keyword uvmMethod           
" uvm_sv/src/base/compatibility/compatibility.svh
"syn keyword uvmClass            
"syn keyword uvmMethod           
" uvm_sv/src/base/compatibility/urm.svh
"syn keyword uvmClass            
"syn keyword uvmMethod           
" uvm_sv/src/base/compatibility/urm_compatibility.svh
"syn keyword uvmClass            
"syn keyword uvmMethod           
" uvm_sv/src/base/compatibility/urm_macro_compatibility.svh
"syn keyword uvmClass            
"syn keyword uvmMethod           
" uvm_sv/src/base/compatibility/urm_message.svh
"syn keyword uvmClass            
"syn keyword uvmMethod           
" uvm_sv/src/base/compatibility/urm_message_compatibility.svh
"syn keyword uvmClass            
"syn keyword uvmMethod           
" uvm_sv/src/base/compatibility/urm_message_defines.svh
"syn keyword uvmClass            
"syn keyword uvmMethod           
" uvm_sv/src/base/compatibility/urm_meth_compatibility.svh
"syn keyword uvmClass            
"syn keyword uvmMethod           
" uvm_sv/src/base/compatibility/urm_port_compatibility.svh
"syn keyword uvmClass            
"syn keyword uvmMethod           
" uvm_sv/src/base/compatibility/urm_type_compatibility.svh
"syn keyword uvmClass            
"syn keyword uvmMethod           
"-------------------------------------------------------------------------------
" uvm_sv/src/methodology/
"-------------------------------------------------------------------------------
" uvm_sv/src/methodology/methodology.svh
syn keyword uvmTypeDef           uvm_default_driver_type uvm_default_sequence_type
syn keyword uvmTypeDef           uvm_default_sequencer_param_type uvm_default_sequencer_type
" uvm_sv/src/methodology/methodology_noparm.svh
" uvm_sv/src/methodology/uvm_agent.svh
syn keyword uvmClass             uvm_agent
syn keyword uvmMethod            run
" uvm_sv/src/methodology/uvm_algorithmic_comparator.svh
syn keyword uvmClass             uvm_algorithmic_comparator
syn keyword uvmMethod            connect get_type_name write
" uvm_sv/src/methodology/uvm_driver.svh
syn keyword uvmClass             uvm_driver
syn keyword uvmMethod            run
" uvm_sv/src/methodology/uvm_in_order_comparator.svh
syn keyword uvmClass             uvm_in_order_comparator
syn keyword uvmMethod            connect flush get_type_name run
syn keyword uvmClass             uvm_in_order_built_in_comparator
syn keyword uvmMethod            get_type_name
syn keyword uvmClass             uvm_in_order_class_comparator
syn keyword uvmMethod            get_type_name
" uvm_sv/src/methodology/uvm_meth_defines.svh
syn keyword uvmTypeDef           uvm_active_passive_enum
" uvm_sv/src/methodology/uvm_monitor.svh
syn keyword uvmClass             uvm_monitor
" uvm_sv/src/methodology/uvm_pair.svh
syn keyword uvmClass             uvm_class_pair
syn keyword uvmMethod            clone comp convert2string copy create get_type_name
syn keyword uvmClass             uvm_built_in_pair
syn keyword uvmMethod            clone comp convert2string copy create get_type_name
" uvm_sv/src/methodology/uvm_policies.svh
syn keyword uvmClass             uvm_built_in_comp
syn keyword uvmMethod            comp
syn keyword uvmClass             uvm_built_in_converter
syn keyword uvmMethod            convert2string
syn keyword uvmClass             uvm_built_in_clone
syn keyword uvmMethod            clone
syn keyword uvmClass             uvm_class_comp
syn keyword uvmMethod            comp
syn keyword uvmClass             uvm_class_converter
syn keyword uvmMethod            convert2string
syn keyword uvmClass             uvm_class_clone
syn keyword uvmMethod            clone
" uvm_sv/src/methodology/uvm_push_driver.svh
syn keyword uvmClass             uvm_push_driver
syn keyword uvmMethod            build check_port_connections end_of_elaboration
" uvm_sv/src/methodology/uvm_random_stimulus.svh
syn keyword uvmClass             uvm_random_stimulus
syn keyword uvmMethod            generate_stimulus get_type_name stop_stimulus_generation
" uvm_sv/src/methodology/uvm_scoreboard.svh
syn keyword uvmClass             uvm_scoreboard
syn keyword uvmMethod            run
" uvm_sv/src/methodology/uvm_subscriber.svh
syn keyword uvmClass             uvm_subscriber
syn keyword uvmMethod            write
" uvm_sv/src/methodology/uvm_test.svh
syn keyword uvmClass             uvm_test
syn keyword uvmMethod            run
"-------------------------------------------------------------------------------
" uvm_sv/src/methodology/layered_stimulus/
"-------------------------------------------------------------------------------
" uvm_sv/src/methodology/layered_stimulus/uvm_layered_stimulus.svh
" uvm_sv/src/methodology/layered_stimulus/uvm_scenario.svh
syn keyword uvmClass             uvm_scenario
syn keyword uvmMethod            apply apply_request apply_send get_id get_scenario_path_name
syn keyword uvmMethod            mid_apply post_apply pre_apply pre_body start
" uvm_sv/src/methodology/layered_stimulus/uvm_scenario_controller.svh
syn keyword uvmClass             uvm_scenario_controller
syn keyword uvmMethod            apply apply_request apply_send
" uvm_sv/src/methodology/layered_stimulus/uvm_scenario_driver.svh
syn keyword uvmClass             uvm_scenario_driver
syn keyword uvmMethod            end_of_elaboration get_next_item run set_scenario_controller
"-------------------------------------------------------------------------------
" uvm_sv/src/methodology/sequences/
"-------------------------------------------------------------------------------
" uvm_sv/src/methodology/sequences/uvm_push_sequencer.svh
syn keyword uvmClass             uvm_push_sequencer
syn keyword uvmMethod            run
" uvm_sv/src/methodology/sequences/uvm_req_rsp_sequence.svh
syn keyword uvmClass             uvm_req_rsp_sequence
syn keyword uvmMethod            apply
" uvm_sv/src/methodology/sequences/uvm_req_rsp_sequence.svh
syn keyword uvmClass             uvm_sequence
syn keyword uvmMethod            do_print start send_request get_current_item get_response put_response
syn keyword uvmMethod            set_sequencer set_response_queue_error_report_disabled
syn keyword uvmMethod            get_response_queue_error_report_disabled set_response_queue_depth get_response_queue_depth
" uvm_sv/src/methodology/sequences/uvm_sequence_base.svh
syn keyword uvmClass             uvm_sequence_base
syn keyword uvmTypeDef           uvm_sequence_state_enum
syn keyword uvmMethod            body create_and_start_sequence_by_name create_item do_sequence_kind get get_priority
syn keyword uvmMethod            get_seq_kind get_sequence get_sequence_by_name get_sequence_state get_sequencer
syn keyword uvmMethod            get_use_response_handler grab is_blocked is_item is_relevant kill m_finish_item
syn keyword uvmMethod            m_get_sqr_sequence_id m_start_item mid_do num_sequences post_body post_do pre_body pre_do
syn keyword uvmMethod            response_handler send_request set_priority set_sequencer stop ungrab unlock use_response_handler
syn keyword uvmMethod            wait_for_grant wait_for_item_done wait_for_relevant wait_for_sequence_state
"syn keyword uvmCompatibility     get_id pre_apply mid_apply post_apply
syn keyword uvmCompatibility     get_parent_scenario
" uvm_sv/src/methodology/sequences/uvm_sequence_builtin.svh
syn keyword uvmClass              uvm_random_sequence
syn keyword uvmMethod             body do_copy do_compare do_print do_record create get_type_name
syn keyword uvmClass              uvm_exhaustive_sequence
syn keyword uvmMethod             body do_copy do_compare do_print do_record create get_type_name
syn keyword uvmClass              uvm_simple_sequence
syn keyword uvmMethod             body create get_type_name
" uvm_sv/src/methodology/sequences/uvm_sequence_item.svh
syn keyword uvmClass             uvm_sequence_item
syn keyword uvmMethod            set_sequence_id get_sequence_id set_use_sequence_info get_use_sequence_info set_id_info set_sequencer
syn keyword uvmMethod            get_sequencer set_parent_sequence get_parent_sequence set_depth get_depth is_item start_item finish_item
syn keyword uvmMethod            m_start_item m_finish_item get_full_name get_root_sequence_name get_root_sequence get_sequence_path
syn keyword uvmMethod            do_print
"syn keyword uvmDeprecated        set_parent_seq get_parent_seq pre_do body mid_do post_do wait_for_grant send_request wait_for_item_done
" uvm_sv/src/methodology/sequences/uvm_sequencer.svh
syn keyword uvmClass             uvm_sequencer
syn keyword uvmTypeDef           uvm_seq_item_prod_if
syn keyword uvmMethod            get_type_name connect build end_of_elaboration send_request get_next_item try_next_item item_done put get peek
syn keyword uvmMethod            m_add_builtin_seqs item_done_trigger item_done_get_trigger_data add_seq_cons_if
syn keyword uvmTypeDef           uvm_virtual_sequencer
syn keyword uvmDeprecatedClass   uvm_seq_prod_if
" uvm_sv/src/methodology/sequences/uvm_sequencer_analysis_fifo.svh
syn keyword uvmClass              sequencer_analysis_fifo
syn keyword uvmMethod             write
" uvm_sv/src/methodology/sequences/uvm_sequencer_base.svh
syn keyword uvmClass              seq_req_class
syn keyword uvmClass              uvm_sequencer_base
syn keyword uvmMethod             do_print user_priority_arbitration grant_queued_locks choose_next_request wait_for_available_sequence
syn keyword uvmMethod             get_seq_item_priority wait_for_arbitration_completed set_arbitration_completed is_child wait_for_grant
syn keyword uvmMethod             wait_for_item_done is_blocked is_locked lock_req unlock_req lock grab unlock ungrab remove_sequence_from_queues
syn keyword uvmMethod             stop_sequences sequence_exiting kill_sequence is_grabbed current_grabber has_do_available set_arbitration
syn keyword uvmMethod             analysis_write wait_for_sequences add_sequence remove_sequence set_sequences_queue get_seq_kind get_sequence
syn keyword uvmMethod             num_sequences send_request
syn keyword uvmDeprecated         start_sequence
" uvm_sv/src/methodology/sequences/uvm_sequencer_param_base.svh
syn keyword uvmClass             uvm_sequencer_param_base
syn keyword uvmMethod            do_print connect build send_request get_current_item put_response analysis_write start_default_sequence run
syn keyword uvmMethod            get_num_reqs_sent get_num_rsps_received set_num_last_reqs get_num_last_reqs last_req set_num_last_rsps
syn keyword uvmMethod            get_num_last_rsps last_rsp execute_item
syn keyword uvmCompatibility     set_num_last_items
"syn keyword uvmCompatibility     last
"-------------------------------------------------------------------------------
" uvm_sv/src/uvm_tlm
"-------------------------------------------------------------------------------
" uvm_sv/src/uvm_tlm/uvm_exports.svh
syn keyword uvmClass             uvm_blocking_get_export uvm_blocking_get_peek_export uvm_blocking_master_export
syn keyword uvmClass             uvm_blocking_peek_export uvm_blocking_put_export uvm_blocking_slave_export
syn keyword uvmClass             uvm_blocking_transport_export uvm_get_export uvm_get_peek_export
syn keyword uvmClass             uvm_master_export uvm_nonblocking_get_export uvm_nonblocking_get_peek_export
syn keyword uvmClass             uvm_nonblocking_master_export uvm_nonblocking_peek_export
syn keyword uvmClass             uvm_nonblocking_put_export uvm_nonblocking_slave_export
syn keyword uvmClass             uvm_nonblocking_transport_export uvm_peek_export uvm_put_export
syn keyword uvmClass             uvm_slave_export uvm_transport_export
syn keyword uvmClass             uvm_analysis_export
syn keyword uvmMethod            get_type_name
" uvm_sv/src/uvm_tlm/uvm_imps.svh
syn keyword uvmClass             uvm_blocking_get_imp uvm_blocking_get_peek_imp uvm_blocking_master_imp
syn keyword uvmClass             uvm_blocking_peek_imp uvm_blocking_put_imp uvm_blocking_slave_imp
syn keyword uvmClass             uvm_blocking_transport_imp uvm_get_imp uvm_get_peek_imp uvm_master_imp
syn keyword uvmClass             uvm_nonblocking_get_imp uvm_nonblocking_get_peek_imp
syn keyword uvmClass             uvm_nonblocking_master_imp uvm_nonblocking_peek_imp
syn keyword uvmClass             uvm_nonblocking_put_imp uvm_nonblocking_slave_imp uvm_nonblocking_transport_imp
syn keyword uvmClass             uvm_peek_imp uvm_put_imp uvm_slave_imp uvm_transport_imp
syn keyword uvmClass             uvm_analysis_imp
syn keyword uvmMethod            writw
" uvm_sv/src/uvm_tlm/uvm_ports.svh
syn keyword uvmClass             uvm_analysis_port uvm_blocking_get_peek_port uvm_blocking_get_port
syn keyword uvmClass             uvm_blocking_master_port uvm_blocking_peek_port uvm_blocking_put_port
syn keyword uvmClass             uvm_blocking_slave_port uvm_blocking_transport_port uvm_get_peek_port
syn keyword uvmClass             uvm_get_port uvm_master_port uvm_nonblocking_get_peek_port uvm_nonblocking_get_port
syn keyword uvmClass             uvm_nonblocking_master_port uvm_nonblocking_peek_port uvm_nonblocking_put_port
syn keyword uvmClass             uvm_nonblocking_slave_port uvm_nonblocking_transport_port uvm_peek_port
syn keyword uvmClass             uvm_put_port uvm_slave_port uvm_transport_port
syn keyword uvmClass             uvm_analysis_port
syn keyword uvmMethod            get_type_name write
" uvm_sv/src/uvm_tlm/sqr_connections.svh
syn keyword uvmClass             uvm_seq_item_pull_port
syn keyword uvmMethod            connect_if
syn keyword uvmMethod            get get_next_item has_do_available peek put put_response try_next_item
syn keyword uvmMethod            item_done wait_for_sequences
syn keyword uvmClass             uvm_seq_item_pull_export
syn keyword uvmMethod            get get_next_item has_do_available peek put put_response try_next_item
syn keyword uvmMethod            item_done wait_for_sequences
syn keyword uvmClass             uvm_seq_item_pull_imp
syn keyword uvmMethod            get get_next_item has_do_available peek put put_response try_next_item
syn keyword uvmMethod            item_done wait_for_sequences
" uvm_sv/src/uvm_tlm/sqr_ifs.svh
syn keyword uvmClass             sqr_if_base
syn keyword uvmMethod            get get_next_item has_do_available item_done peek put put_response try_next_item wait_for_sequences
" uvm_sv/src/uvm_tlm/uvm_tlm.svh
" uvm_sv/src/uvm_tlm/uvm_tlm_fifo_base.svh
syn keyword uvmClass             uvm_tlm_event
syn keyword uvmClass             uvm_tlm_fifo_base
syn keyword uvmMethod            can_get can_peek can_put flush get is_empty ok_to_get ok_to_peek
syn keyword uvmMethod            ok_to_put peek put size try_get try_peek try_put used
" uvm_sv/src/uvm_tlm/uvm_tlm_fifos.svh
syn keyword uvmClass             uvm_tlm_fifo
syn keyword uvmMethod            can_get can_peek can_put flush get get_type_name is_empty
syn keyword uvmMethod            is_full peek put size try_get try_peek try_put used
syn keyword uvmClass             uvm_tlm_analysis_fifo
syn keyword uvmMethod            get_type_name write
" uvm_sv/src/uvm_tlm/uvm_tlm_ifs.svh
syn keyword uvmClass             uvm_tlm_if_base
syn keyword uvmMethod            can_get can_peek can_put get nb_transport peek put
syn keyword uvmMethod            transport try_get try_peek try_put write
" uvm_sv/src/uvm_tlm/uvm_tlm_imps.svh
" uvm_sv/src/uvm_tlm/uvm_tlm_req_rsp.svh
syn keyword uvmClass             uvm_tlm_req_rsp_channel
syn keyword uvmMethod            create create_aliased_exports connect get_type_name
syn keyword uvmClass             uvm_tlm_transport_channel
syn keyword uvmMethod            nb_transport transport
 
syn keyword uvmMethod            main_phase end_of_elaboration_phase start_of_simulation_phase run_phase
syn keyword uvmMethod            configure_phase reset_phase final_phase build_phase connect_phase check_phase
syn keyword uvmMethod            phase raise_objection drop_objection pre_reset_phase
syn keyword uvmMethod            report_phase uvm_config_db uvm_phase post_randomize
syn keyword uvmMethod            pre_randomize post_reset_phase pre_configure_phase
syn keyword uvmMethod            post_configure_phase pre_main_phase uvm_pre_main_phase post_main_phase
syn keyword uvmMethod            pre_shutdown_phase shutdown_phase post_shutdown_phase type_id p_sequencer 
syn keyword uvmMethod            uvm_report_catcher seq_item_export seq_item_port process
" uvm_sv/src/dpi/   by sqlmap
syn keyword uvmMethod            uvm_hdl_force uvm_hdl_read uvm_hdl_deposit uvm_hdl_release uvm_hdl_check_path
syn keyword uvmMethod            uvm_hdl_force_time uvm_hdl_release_and_read uvm_re_match uvm_dump_re_cache uvm_glob_to_re
syn keyword uvmTypeDef           uvm_hdl_data_t
syn keyword uvmMethod            uvm_dpi_get_next_arg  uvm_dpi_get_tool_name  uvm_dpi_get_tool_version uvm_dpi_regcomp uvm_dpi_regexec uvm_dpi_regfree
 
"ToDo markers:
syn match   uvmComment	        "//.*$" contains=uvmTodo,@Spell
syn keyword uvmTodo             TODO FIXME XXX !!! TBD QA contained
" Define the default highlighting.
" For version 5.7 and earlier: only when not done already
" For version 5.8 and later: only when an item doesn't have highlighting yet
if version >= 508 || !exists("did_verilog_syn_inits")
   if version < 508
      let did_verilog_syn_inits = 1
      command -nargs=+ HiLink hi link <args>
   else
      command -nargs=+ HiLink hi def link <args>
   endif
   " The default highlighting.
   HiLink verilogMethod          Function
   HiLink verilogTypeDef         TypeDef
   HiLink verilogAssertion       Include
   HiLink uvmClass               Type
   HiLink uvmTypeDef             Type
   HiLink uvmMethod              Function
   HiLink uvmMethodGlobal        Function
   HiLink uvmDeprecated          Error
   HiLink uvmDeprecatedClass     Error
   HiLink uvmDeprecatedMethod    Error
   HiLink uvmCompatibility       Underlined
   HiLink uvmComment	         Comment
   HiLink uvmTodo                Todo
   delcommand HiLink
endif
let b:current_syntax = "systemverilog"
" vim: ts=8
 
 
 
 
