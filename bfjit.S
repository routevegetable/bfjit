
  .text
  .global xlate_call_slow
xlate_call_slow:
  mov %rsp, %rdi
  call runtime_call_slow        // My work here is done


  .global runtime_enter
runtime_enter:
  mov %rsi, %rsp                      // Gonna need this
  mov %rsp, %rbp                      // Why not?
  mov xlate_rax_spill(%rip),%rax      // Restore this crap
  jmp *%rdi                           // Fuck off
