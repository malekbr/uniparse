let () = Memtrace.trace_if_requested ()
let () = Inline_benchmarks_public.Runner.main ~libname:"uniparse"
