/* C smoke client for the language-neutral embedding interface: includes
 * the public header, links the host static library, calls representative
 * one-shot and handle APIs, and frees every returned value. This client
 * proves the interface independently of Swift and is the template for
 * future bindings (ADR 0047). */

#include <stdio.h>
#include <string.h>

#include "talk_ffi.h"

static int failures = 0;

static void expect(int condition, const char *what) {
    if (!condition) {
        fprintf(stderr, "smoke: FAIL: %s\n", what);
        failures++;
    }
}

int main(void) {
    expect(talk_ffi_abi_version() == TALK_FFI_ABI_VERSION, "ABI version agrees with the header");

    /* One-shot TalkResult API. */
    TalkResult version = talk_version_utf8();
    expect(version.status == TALK_STATUS_OK, "talk_version_utf8 succeeds");
    expect(version.data.ptr != NULL && version.data.len > 0, "version carries a payload");
    talk_result_free(version);

    const char *source = "1 + 2\n";
    TalkResult formatted = talk_format_utf8((const uint8_t *)source, strlen(source));
    expect(formatted.status == TALK_STATUS_OK, "talk_format_utf8 succeeds");
    expect(
        formatted.data.len == strlen(source)
            && memcmp(formatted.data.ptr, source, formatted.data.len) == 0,
        "formatting an already-formatted program is a fixed point"
    );
    talk_result_free(formatted);

    /* One-shot handle API with borrowed views. */
    const char *path = "smoke.tlk";
    TalkDiagnostics *diagnostics = talk_check_utf8(
        (const uint8_t *)path,
        strlen(path),
        (const uint8_t *)source,
        strlen(source)
    );
    expect(diagnostics != NULL, "talk_check_utf8 returns a handle");
    expect(talk_diagnostics_status(diagnostics) == TALK_STATUS_OK, "check handle reports OK");
    expect(talk_diagnostics_count(diagnostics) == 0, "a valid program has no diagnostics");
    talk_diagnostics_free(diagnostics);

    /* Stateful handle API. */
    TalkReplSession *repl = talk_repl_new();
    expect(repl != NULL, "talk_repl_new returns a session");
    const char *line = "40 + 2";
    TalkEvalResult *eval = talk_repl_eval_utf8(repl, (const uint8_t *)line, strlen(line));
    expect(eval != NULL, "talk_repl_eval_utf8 returns a handle");
    expect(talk_eval_result_status(eval) == TALK_STATUS_OK, "REPL evaluation reports OK");
    talk_eval_result_free(eval);
    talk_repl_free(repl);

    /* Invalid UTF-8 is rejected, not misparsed. */
    const uint8_t invalid[] = {0xFF, 0xFE};
    TalkResult bad = talk_format_utf8(invalid, sizeof invalid);
    expect(bad.status == TALK_STATUS_INVALID_INPUT, "invalid UTF-8 yields INVALID_INPUT");
    talk_result_free(bad);

    if (failures != 0) {
        fprintf(stderr, "smoke: %d check(s) failed\n", failures);
        return 1;
    }
    printf("smoke: ok\n");
    return 0;
}
