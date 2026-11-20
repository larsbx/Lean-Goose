// Appended only to the exactly reconstructed diagnostic harness. The original
// checker remains byte-identical apart from its unique main entrypoint rename.
// This driver calls the real lift/substitute functions and serializes raw data;
// it performs no substitution, shifting, type inference, or scope calculation.
fn main() {
    let argv = args();
    if argv.len != 6 && argv.len != 7 {
        parse_failure("usage: --lift|--substitute fixture root parameter cutoff [operation-fuel]");
    }
    let is_lift = argv[1] == "--lift";
    if !is_lift && argv[1] != "--substitute" { parse_failure("unknown transformation operation"); }
    var text: u8[>..] = [];
    if !read_file(argv[2], text) { parse_failure("cannot read fixture"); }
    if text.len > MAX_TRACE_INPUT_BYTES { trace_failure("input bytes exceed trace bound"); }
    var raw: Node[>..] = [];
    var definitions: Definition[>..] = [];
    parse(text, raw, definitions);
    if raw.len > MAX_TRACE_NODES { trace_failure("input nodes exceed trace bound"); }
    if definitions.len != 1 || definitions[0].name != "transformation"
        || definitions[0].ty != 0 || definitions[0].value != 0 {
        parse_failure("invalid transformation sentinel");
    }
    let root = natural(argv[3]);
    let parameter = natural(argv[4]);
    let cutoff = natural(argv[5]);
    if root >= raw.len { parse_failure("transformation root outside arena"); }
    if !is_lift && parameter >= raw.len { parse_failure("replacement root outside arena"); }
    let budget = if argv.len == 7 { natural(argv[6]) } else { CHECK_FUEL };
    var nodes: Node[>..] = [];
    var env: Binding[>..] = [];
    var context: i64[>..<] = [];
    var s = State { nodes: nodes, env: env, context: context };
    import_nodes(s, raw);
    // Operation-fuel controls begin after normal import, so an import refusal
    // cannot masquerade as a witnessed transformation failure.
    s.fuel = budget;
    let result = if is_lift { lift(s, root, parameter, cutoff, 1) }
                 else { substitute(s, root, parameter, cutoff, 1) };
    if nodes.len > MAX_TRACE_NODES { trace_failure("derived nodes exceed trace bound"); }
    var output: u8[>..] = [];
    trace_append(output, "{\"schema\":\"lean-goose.substitution-trace.v1\",\"engine\":\"goose-aot\",\"status\":\"");
    trace_append(output, if s.error == 0 { "transformed" } else { "halted" });
    trace_append(output, "\",\"operation\":\"");
    trace_append(output, if is_lift { "lift" } else { "substitute" });
    trace_append(output, "\",\"root\":");
    trace_number(output, root);
    trace_append(output, ",\"parameter\":");
    trace_number(output, parameter);
    trace_append(output, ",\"cutoff\":");
    trace_number(output, cutoff);
    trace_append(output, ",\"fuel_budget\":");
    trace_number(output, budget);
    trace_append(output, ",\"result\":");
    if s.error == 0 { trace_number(output, result); }
    else { trace_append(output, "null"); }
    trace_append(output, ",\"error\":");
    trace_number(output, s.error);
    trace_append(output, ",\"snapshot\":");
    trace_snapshot(output, Definition { name: "transformation", ty: 0, value: 0 }, s.error, nodes, env);
    trace_append(output, ",\"acceptance_authority\":false}");
    print(output);
    if s.error != 0 { execution_error(s.error); }
}
