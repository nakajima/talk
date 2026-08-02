/* Pointer ABI between generated LLVM IR and the C runtime.
 *
 * The language functions themselves are LLVM functions. This file only owns
 * services that genuinely need a runtime: allocation, effects, host IO,
 * regions, rendering, and checked operations. Keeping TalkValue behind
 * pointers here avoids baking a platform's aggregate calling convention into
 * generated IR.
 */

extern void talk_llvm_dispatch(TalkValue *out, uint32_t function,
                               const TalkValue *env, const TalkValue *args);

static TalkValue talk_dispatch(uint32_t function, const TalkValue *env,
                               const TalkValue *args) {
    TalkValue out = talk_unit();
    talk_llvm_dispatch(&out, function, env, args);
    return out;
}

_Static_assert(sizeof(TalkValue) == 16, "LLVM TalkValue size disagrees with C");
_Static_assert(offsetof(TalkValue, v) == 8, "LLVM TalkValue payload offset disagrees with C");

void talk_llvm_frame_enter(void) { talk_frame_enter(); }
uint32_t talk_llvm_enter(size_t *depth) {
    *depth = talk_depth;
    return talk_enter();
}
void talk_llvm_leave(void) { talk_leave(); }
int talk_llvm_unwinding(void) { return talk_unwinding; }
int talk_llvm_unwind_targets(size_t depth, uint32_t frame) {
    return talk_unwind_targets(depth, frame);
}
void talk_llvm_unwind_take(TalkValue *out) { *out = talk_unwind_take(); }
int talk_llvm_cont_is(const TalkValue *cont, size_t depth, uint32_t frame) {
    return talk_cont_depth(*cont) == depth && talk_cont_frame(*cont) == frame;
}
void talk_llvm_cont(TalkValue *out, size_t depth, uint32_t frame) {
    *out = talk_cont(depth, frame);
}
void talk_llvm_push_handler(uint32_t effect, const TalkValue *clause,
                            const TalkValue *cont, size_t depth, uint32_t frame) {
    talk_push_handler(effect, *clause, *cont, depth, frame);
}
void talk_llvm_find_handler(uint32_t effect, TalkValue *clause,
                            TalkValue *cont, TalkValue *index) {
    talk_find_handler(effect, clause, cont, index);
}
void talk_llvm_get_floor(TalkValue *out) { *out = talk_get_floor(); }
void talk_llvm_set_floor(const TalkValue *value) { talk_set_floor(*value); }
void talk_llvm_abort_to(const TalkValue *cont, const TalkValue *value) {
    talk_abort_to(*cont, *value);
}

void talk_llvm_checked_scalar(TalkValue *out, uint32_t op,
                              const TalkValue *a, const TalkValue *b) {
    switch (op) {
    case 0: *out = talk_div(*a, *b); return;
    case 1: *out = talk_float_to_int(*a); return;
    case 2: *out = talk_int_to_byte(*a); return;
    default: talk_trap("unknown checked scalar operation");
    }
}

void talk_llvm_agg(TalkValue *out, uint32_t symbol, uint32_t tag, uint32_t len) {
    *out = talk_agg(symbol, tag, len);
}
void talk_llvm_agg_set(TalkValue *aggregate, uint32_t index,
                       const TalkValue *value) {
    aggregate->v.agg->fields[index] = *value;
}
void talk_llvm_agg_get(TalkValue *out, const TalkValue *aggregate, uint32_t index) {
    *out = aggregate->v.agg->fields[index];
}
int64_t talk_llvm_agg_tag(const TalkValue *aggregate) {
    return (int64_t)aggregate->v.agg->tag;
}
void talk_llvm_set_field(TalkValue *record, uint32_t index,
                         const TalkValue *value) {
    *record = talk_set_field(*record, index, *value);
}

void talk_llvm_string(TalkValue *out, uint32_t offset, uint32_t len,
                      uint32_t string_symbol, uint32_t storage_symbol) {
    TalkValue storage = talk_agg(storage_symbol, 0, 1);
    storage.v.agg->fields[0] = talk_pointer(talk_statics + offset);
    TalkValue string = talk_agg(string_symbol, 0, 3);
    string.v.agg->fields[0] = storage;
    string.v.agg->fields[1] = talk_int((int64_t)len);
    string.v.agg->fields[2] = talk_int((int64_t)len);
    *out = string;
}
void talk_llvm_bytes(TalkValue *out, uint32_t offset) {
    *out = talk_pointer(talk_statics + offset);
}

void talk_llvm_closure(TalkValue *out, uint32_t function, uint32_t captured) {
    *out = talk_closure(function, captured);
}
uint32_t talk_llvm_closure_function(const TalkValue *closure) {
    return closure->v.agg->tag;
}
const TalkValue *talk_llvm_closure_env(const TalkValue *closure) {
    return closure->v.agg->fields;
}
void talk_llvm_cell_new(TalkValue *out, const TalkValue *initial) {
    *out = talk_cell_new(*initial);
}
void talk_llvm_cell_get(TalkValue *out, const TalkValue *cell) {
    *out = talk_cell_get(*cell);
}
void talk_llvm_cell_set(const TalkValue *cell, const TalkValue *value) {
    talk_cell_set(*cell, *value);
}
void talk_llvm_existential_payload(TalkValue *out, const TalkValue *value) {
    *out = talk_existential_payload(*value);
}
void talk_llvm_existential_witness(TalkValue *out, const TalkValue *value,
                                   uint32_t index) {
    *out = talk_existential_witness(*value, index);
}
void talk_llvm_get_element(TalkValue *out, const TalkValue *value,
                           const TalkValue *index) {
    *out = talk_get_element(*value, *index);
}

void talk_llvm_alloc(TalkValue *out, const TalkValue *bytes) {
    *out = talk_alloc(*bytes);
}
void talk_llvm_free(const TalkValue *value) { talk_free(*value); }
void talk_llvm_retain(const TalkValue *value) { talk_retain(*value); }
void talk_llvm_is_unique(TalkValue *out, const TalkValue *value) {
    *out = talk_is_unique(*value);
}
void talk_llvm_ptr_add(TalkValue *out, const TalkValue *pointer,
                       const TalkValue *offset, uint32_t size) {
    *out = talk_ptr_add(*pointer, *offset, size);
}
void talk_llvm_mem_copy(const TalkValue *from, const TalkValue *to,
                        const TalkValue *len) {
    talk_mem_copy(*from, *to, *len);
}
void talk_llvm_load(TalkValue *out, const TalkValue *pointer, uint32_t kind) {
    switch (kind) {
    case 0: *out = talk_load_byte(*pointer); return;
    case 1: *out = talk_load_i64(*pointer); return;
    case 2: *out = talk_load_f64(*pointer); return;
    case 3: *out = talk_load_bool(*pointer); return;
    case 4: *out = talk_load_ptr(*pointer); return;
    case 5: *out = talk_load_boxed(*pointer); return;
    default: talk_trap("unknown memory load kind");
    }
}
void talk_llvm_store(const TalkValue *pointer, const TalkValue *value,
                     uint32_t kind) {
    switch (kind) {
    case 0: talk_store_byte(*pointer, *value); return;
    case 1: case 3: talk_store_word(*pointer, value->v.i); return;
    case 2: talk_store_f64(*pointer, *value); return;
    case 4: talk_store_ptr(*pointer, *value); return;
    case 5: talk_store_boxed(*pointer, *value); return;
    default: talk_trap("unknown memory store kind");
    }
}
void talk_llvm_global_load(TalkValue *out, uint32_t global) {
    *out = talk_load_boxed(talk_pointer(talk_globals + (size_t)global * 8));
}
void talk_llvm_global_store(uint32_t global, const TalkValue *value) {
    talk_store_boxed(talk_pointer(talk_globals + (size_t)global * 8), *value);
}

void talk_llvm_object_new(TalkValue *out, uint32_t fields) {
    *out = talk_object_new(fields);
}
void talk_llvm_object_get(TalkValue *out, const TalkValue *object, uint32_t index) {
    *out = object->v.obj->fields[index];
}
void talk_llvm_object_set(const TalkValue *object, uint32_t index,
                          const TalkValue *value) {
    talk_object_set(*object, index, *value);
}
void talk_llvm_region_acquire(const TalkValue *value) {
    talk_region_acquire(*value);
}
void talk_llvm_region_release(const TalkValue *value) {
    talk_region_release(*value);
}
void talk_llvm_set_finalizer(const TalkValue *object,
                             const TalkValue *closure) {
    object->v.obj->finalizer = *closure;
}
void talk_llvm_io(TalkValue *out, uint8_t op, const TalkValue *a,
                  const TalkValue *b, const TalkValue *c) {
    *out = talk_int(talk_io(op, *a, *b, *c));
}
void talk_llvm_trap(const char *message) { talk_trap(message); }
