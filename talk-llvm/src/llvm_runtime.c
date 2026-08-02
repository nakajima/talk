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

static TalkValue talk_native_retag(TalkValue value) {
    if (value.tag == TALK_NATIVE) {
        talk_trap("LLVM backend received an unexpected native aggregate");
    }
    return value;
}

static TalkValue talk_rebox(uint32_t layout, TalkValue flat) {
    (void)layout;
    return flat;
}

static void talk_native_scan(TalkValue value, struct TalkObject ***out,
                             size_t *count, size_t *capacity) {
    (void)value;
    (void)out;
    (void)count;
    (void)capacity;
}

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

static const TalkField *talk_llvm_agg_site(uint32_t layout, uint32_t tag,
                                           uint32_t index) {
    if (layout >= talk_layout_count) {
        talk_trap("aggregate references an unknown layout");
    }
    const TalkLayoutInfo *shape = &talk_layouts[layout];
    if (!shape->is_sum) {
        if (index >= shape->field_count) {
            talk_trap("aggregate argument index out of range");
        }
        return &shape->fields[index];
    }
    if (tag >= shape->variant_count) {
        talk_trap("aggregate tag out of range");
    }
    uint32_t start = shape->variant_starts[tag];
    uint32_t end = shape->variant_starts[tag + 1];
    if (start + index >= end) {
        talk_trap("aggregate payload index out of range");
    }
    return &shape->fields[start + index];
}

void talk_llvm_agg(TalkValue *out, uint32_t layout, uint32_t symbol,
                   uint32_t tag) {
    if (layout >= talk_layout_count) {
        talk_trap("aggregate references an unknown layout");
    }
    const TalkLayoutInfo *shape = &talk_layouts[layout];
    *out = talk_agg(layout, symbol, 0, shape->width);
    for (uint32_t index = 0; index < shape->width; index++) {
        out->v.agg->fields[index] = talk_unit();
    }
    if (shape->is_sum) {
        if (shape->width == 0) {
            talk_trap("sum layout has no tag slot");
        }
        out->v.agg->fields[0] = talk_int((int64_t)tag);
    }
}

void talk_llvm_agg_arg(TalkValue *aggregate, uint32_t layout, uint32_t tag,
                       uint32_t index, const TalkValue *value) {
    const TalkField *site = talk_llvm_agg_site(layout, tag, index);
    if (site->child == UINT32_MAX) {
        aggregate->v.agg->fields[site->offset] = *value;
        return;
    }
    if (site->width == 0) {
        return;
    }
    TalkValue flat = *value;
    if (flat.tag == TALK_NATIVE) {
        flat = talk_native_retag(flat);
    }
    memcpy(aggregate->v.agg->fields + site->offset, flat.v.agg->fields,
           (size_t)site->width * sizeof(TalkValue));
}

void talk_llvm_dyn_agg(TalkValue *out, uint32_t symbol, uint32_t len) {
    *out = talk_agg(TALK_DYN, symbol, 0, len);
}

void talk_llvm_agg_set(TalkValue *aggregate, uint32_t index,
                       const TalkValue *value) {
    aggregate->v.agg->fields[index] = *value;
}

void talk_llvm_field(TalkValue *out, const TalkValue *aggregate,
                     uint32_t container, uint32_t offset, uint32_t member,
                     uint32_t member_symbol) {
    (void)container;
    if (member == UINT32_MAX) {
        *out = aggregate->v.agg->fields[offset];
        return;
    }
    if (member >= talk_layout_count) {
        talk_trap("field references an unknown member layout");
    }
    uint32_t width = talk_layouts[member].width;
    if (width == 0) {
        *out = talk_unit();
        return;
    }
    *out = talk_rebox(member,
                      talk_slice(*aggregate, offset, width, member, member_symbol));
}

void talk_llvm_field_index(TalkValue *out, const TalkValue *aggregate,
                           uint32_t index) {
    *out = talk_native_field(*aggregate, index);
}

int64_t talk_llvm_agg_tag(const TalkValue *aggregate) {
    return aggregate->v.agg->fields[0].v.i;
}

static void talk_llvm_replace_slots(TalkValue *record, const TalkValue *value,
                                    uint32_t offset, uint32_t member) {
    if (member == UINT32_MAX) {
        *record = talk_set_slots(*record, offset, 1, *value);
        return;
    }
    if (member >= talk_layout_count) {
        talk_trap("field write references an unknown member layout");
    }
    uint32_t span = talk_layouts[member].width;
    if (span == 0) {
        return;
    }
    TalkValue flat = *value;
    if (flat.tag == TALK_NATIVE) {
        flat = talk_native_retag(flat);
    }
    TalkAgg *from = record->v.agg;
    TalkValue copy = talk_agg(from->layout, from->symbol, from->meta, from->len);
    memcpy(copy.v.agg->fields, from->fields,
           (size_t)from->len * sizeof(TalkValue));
    memcpy(copy.v.agg->fields + offset, flat.v.agg->fields,
           (size_t)span * sizeof(TalkValue));
    *record = copy;
}

void talk_llvm_set_field(TalkValue *record, const TalkValue *value,
                         uint32_t container, uint32_t offset, uint32_t member) {
    (void)container;
    talk_llvm_replace_slots(record, value, offset, member);
}

void talk_llvm_set_field_index(TalkValue *record, const TalkValue *value,
                               uint32_t index) {
    if (record->tag == TALK_NATIVE) {
        *record = talk_native_retag(*record);
    }
    uint32_t layout = record->v.agg->layout;
    if (layout == TALK_DYN || layout >= talk_layout_count) {
        talk_llvm_replace_slots(record, value, index, UINT32_MAX);
        return;
    }
    if (index >= talk_layouts[layout].field_count) {
        talk_trap("field write index out of range");
    }
    const TalkField *site = &talk_layouts[layout].fields[index];
    talk_llvm_replace_slots(record, value, site->offset, site->child);
}

void talk_llvm_string(TalkValue *out, uint32_t offset, uint32_t len,
                      uint32_t string_layout, uint32_t storage_layout,
                      uint32_t string_symbol, uint32_t storage_symbol) {
    TalkValue storage;
    talk_llvm_agg(&storage, storage_layout, storage_symbol, 0);
    TalkValue pointer = talk_pointer(talk_statics + offset);
    talk_llvm_agg_arg(&storage, storage_layout, 0, 0, &pointer);
    talk_llvm_agg(out, string_layout, string_symbol, 0);
    TalkValue length = talk_int((int64_t)len);
    talk_llvm_agg_arg(out, string_layout, 0, 0, &storage);
    talk_llvm_agg_arg(out, string_layout, 0, 1, &length);
    talk_llvm_agg_arg(out, string_layout, 0, 2, &length);
}
void talk_llvm_bytes(TalkValue *out, uint32_t offset) {
    *out = talk_pointer(talk_statics + offset);
}

void talk_llvm_closure(TalkValue *out, uint32_t function, uint32_t captured) {
    *out = talk_closure(function, captured);
}
uint32_t talk_llvm_closure_function(const TalkValue *closure) {
    return closure->v.agg->meta;
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
                           const TalkValue *index, uint32_t element,
                           uint32_t element_symbol) {
    if (element < talk_layout_count && talk_layouts[element].width != 1) {
        *out = talk_get_element_slice(*value, *index,
                                      talk_layouts[element].width, element,
                                      element_symbol);
    } else {
        *out = talk_get_element(*value, *index);
    }
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
