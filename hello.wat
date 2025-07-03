;; hello.wat
(module
  ;; Import the required fd_write WASI function
  (import "wasi_snapshot_preview1" "fd_write"
    (func $fd_write (param i32 i32 i32 i32) (result i32)))
  
  ;; Memory with initial size of 1 page (64KB)
  (memory 1)
  (export "memory" (memory 0))
  
  ;; Store the string at offset 0
  (data (i32.const 0) "Hello, World from WebAssembly!\n")
  
  ;; The _start function (entry point)
  (func $main (export "_start")
    ;; Create iovec structure at offset 32
    ;; iovec.iov_base = 0 (string location)
    (i32.store (i32.const 32) (i32.const 0))
    ;; iovec.iov_len = 31 (string length)
    (i32.store (i32.const 36) (i32.const 31))
    
    ;; Call fd_write(stdout=1, iovec_ptr=32, iovec_count=1, written_ptr=40)
    (call $fd_write
      (i32.const 1)    ;; stdout
      (i32.const 32)   ;; iovec pointer
      (i32.const 1)    ;; iovec count
      (i32.const 40)   ;; where to store bytes written
    )
    drop ;; Ignore the return value
  )
)
