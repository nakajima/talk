/* The shared library-boundary harness (ADR 0048), driven identically
 * against the C and LLVM backend artifacts. It takes the VM oracle's
 * answers as arguments -- expected_double expected_length expected_total
 * expected_handled -- so agreement with the interpreter is part of every
 * run. Each failing step exits with its own code so a regression names
 * itself. */

#include "mylib.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fail(int code, const char *what) {
    fprintf(stderr, "harness: %s (last error: %s)\n", what, mylib_error_message());
    return code;
}

int main(int argc, char **argv) {
    if (argc != 5) {
        fprintf(stderr, "usage: harness DOUBLE LENGTH TOTAL HANDLED\n");
        return 2;
    }
    long long expected_double = atoll(argv[1]);
    long long expected_length = atoll(argv[2]);
    long long expected_total = atoll(argv[3]);
    long long expected_handled = atoll(argv[4]);

    /* Lifecycle. */
    if (mylib_init() != MYLIB_OK) return fail(10, "init failed");
    if (mylib_init() != MYLIB_ERR_STATE) return fail(11, "double init must be rejected");

    mylib_value args[1];
    mylib_value out = mylib_unit();

    /* Scalars. */
    args[0] = mylib_int(21);
    if (mylib_double(&out, args, 1) != MYLIB_OK) return fail(12, "double failed");
    if (out.tag != MYLIB_TAG_INT) return fail(13, "double result tag");
    if (mylib_value_int(out) != expected_double) return fail(14, "double result value");

    /* Arity is checked before generated code runs. */
    if (mylib_double(&out, args, 2) != MYLIB_ERR_ARITY) return fail(15, "arity must be checked");
    if (strstr(mylib_error_message(), "double") == NULL) return fail(16, "arity message");

    /* Strings round-trip the boundary and stay valid across calls. */
    mylib_value greeting = mylib_unit();
    if (mylib_greet(&greeting, NULL, 0) != MYLIB_OK) return fail(17, "greet failed");
    args[0] = greeting;
    mylib_value shouted = mylib_unit();
    if (mylib_shout(&shouted, args, 1) != MYLIB_OK) return fail(18, "shout failed");
    args[0] = shouted;
    if (mylib_length(&out, args, 1) != MYLIB_OK) return fail(19, "length failed");
    if (mylib_value_int(out) != expected_length) return fail(20, "length result value");

    /* Aggregates round-trip the boundary. */
    args[0] = mylib_int(20);
    mylib_value made = mylib_unit();
    if (mylib_pair(&made, args, 1) != MYLIB_OK) return fail(21, "pair failed");
    args[0] = made;
    if (mylib_total(&out, args, 1) != MYLIB_OK) return fail(22, "total failed");
    if (mylib_value_int(out) != expected_total) return fail(23, "total result value");

    /* Effects handled inside generated code work per invocation. */
    args[0] = mylib_int(4);
    if (mylib_handled(&out, args, 1) != MYLIB_OK) return fail(24, "handled failed");
    if (mylib_value_int(out) != expected_handled) return fail(25, "handled result value");
    if (mylib_handled(&out, args, 1) != MYLIB_OK) return fail(26, "handled must repeat");
    if (mylib_value_int(out) != expected_handled) return fail(27, "repeated handled value");

    /* A trap becomes a status, never a process exit. */
    args[0] = mylib_int(0);
    if (mylib_crash(&out, args, 1) != MYLIB_ERR_TRAP) return fail(28, "trap must become a status");
    if (strstr(mylib_error_message(), "division by zero") == NULL) return fail(29, "trap message");

    /* A failed invocation performed complete cleanup: uninitialized
     * until the owner re-inits. */
    args[0] = mylib_int(21);
    if (mylib_double(&out, args, 1) != MYLIB_ERR_STATE) return fail(30, "post-trap calls must be rejected");
    if (mylib_init() != MYLIB_OK) return fail(31, "re-init after trap failed");
    if (mylib_double(&out, args, 1) != MYLIB_OK) return fail(32, "post-re-init call failed");
    if (mylib_value_int(out) != expected_double) return fail(33, "post-re-init result");

    /* An exit request is contained the same way, carrying its status. */
    args[0] = mylib_int(3);
    if (mylib_leave(&out, args, 1) != MYLIB_ERR_EXIT) return fail(34, "exit must become a status");
    if (mylib_exit_status() != 3) return fail(35, "exit status value");
    if (strstr(mylib_error_message(), "status 3") == NULL) return fail(36, "exit message");
    if (mylib_double(&out, args, 1) != MYLIB_ERR_STATE) return fail(37, "post-exit calls must be rejected");
    if (mylib_init() != MYLIB_OK) return fail(38, "re-init after exit failed");
    args[0] = mylib_int(21);
    if (mylib_double(&out, args, 1) != MYLIB_OK) return fail(39, "post-exit re-init call failed");

    mylib_teardown();
    /* Teardown is idempotent and a torn-down library rejects calls. */
    mylib_teardown();
    if (mylib_double(&out, args, 1) != MYLIB_ERR_STATE) return fail(40, "post-teardown calls must be rejected");
    return 0;
}
