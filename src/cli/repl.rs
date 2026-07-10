use std::{
    borrow::Cow,
    io::{self, BufRead, IsTerminal, Write},
    path::PathBuf,
};

use rustyline::{
    CompletionType, Config, EditMode, Editor, Helper,
    completion::{Completer, Pair},
    error::ReadlineError,
    highlight::{CmdKind, Highlighter},
    hint::Hinter,
    history::DefaultHistory,
    validate::{ValidationContext, ValidationResult, Validator},
};

use crate::{
    cli::diagnostics::{ColorMode, render_text},
    highlighter::{Higlighter as TalkHighlighter, Kind as HighlightKind},
    repl::{ReplEvalResult, ReplSession},
};

const PRIMARY_PROMPT: &[u8] = b"talk> ";
const CONTINUATION_PROMPT: &[u8] = b"....> ";
const HISTORY_FILE_NAME: &str = ".talk_history";

pub fn run() {
    let mut repl = Repl::new(ReplSession::new());
    if let Err(err) = repl.run() {
        eprintln!("repl error: {err}");
    }
}

struct Repl {
    session: ReplSession,
}

impl Repl {
    fn new(session: ReplSession) -> Self {
        Self { session }
    }

    fn run(&mut self) -> io::Result<()> {
        let stdin = io::stdin();
        let stdout = io::stdout();
        if stdin.is_terminal() && stdout.is_terminal() {
            return self.run_interactive();
        }

        let mut input = stdin.lock();
        let mut output = stdout.lock();
        let stderr = io::stderr();
        let mut error = stderr.lock();

        self.run_with(&mut input, &mut output, &mut error)
    }

    fn run_interactive(&mut self) -> io::Result<()> {
        let use_color = terminal_color_enabled();
        let config = Config::builder()
            .history_ignore_space(true)
            .completion_type(CompletionType::List)
            .edit_mode(EditMode::Emacs)
            .build();
        let mut editor = Editor::<ReplHelper, DefaultHistory>::with_config(config)
            .map_err(readline_to_io_error)?;
        editor.set_helper(Some(ReplHelper::new(&self.session, use_color)));
        let history_path = history_path();
        if let Some(path) = &history_path {
            let _ = editor.load_history(path);
        }

        self.print_banner(use_color)?;

        let mut entry = 1usize;
        loop {
            self.sync_editor_helper(&mut editor, use_color);
            let prompt = format!("talk[{entry}]> ");
            match editor.readline(&prompt) {
                Ok(input_source) => {
                    if !input_source.trim().is_empty() {
                        let _ = editor.add_history_entry(input_source.as_str());
                    }

                    let mut output = io::stdout().lock();
                    let mut error = io::stderr().lock();
                    let should_continue =
                        self.handle_input(&input_source, &mut output, &mut error)?;
                    if !should_continue {
                        break;
                    }
                    entry += 1;
                }
                Err(ReadlineError::Interrupted) => {
                    writeln!(io::stderr(), "interrupted")?;
                    break;
                }
                Err(ReadlineError::Eof) => break,
                Err(err) => return Err(readline_to_io_error(err)),
            }
        }

        if let Some(path) = &history_path
            && let Err(err) = editor.append_history(path)
        {
            eprintln!(
                "warning: failed to save REPL history to {}: {err}",
                path.display()
            );
        }

        Ok(())
    }

    fn print_banner(&self, use_color: bool) -> io::Result<()> {
        let mut output = io::stdout().lock();
        if use_color {
            writeln!(output, "\x1b[1;36mtalk repl\x1b[0m")?;
        } else {
            writeln!(output, "talk repl")?;
        }
        writeln!(output, "type /help for commands, /quit to exit")?;
        writeln!(output)
    }

    fn sync_editor_helper(&self, editor: &mut Editor<ReplHelper, DefaultHistory>, use_color: bool) {
        if let Some(helper) = editor.helper_mut() {
            helper.set_session(&self.session, use_color);
        }
    }

    fn run_with<R: BufRead, W: Write, E: Write>(
        &mut self,
        input: &mut R,
        output: &mut W,
        error: &mut E,
    ) -> io::Result<()> {
        loop {
            let Some(input_source) = self.read_input(input, output)? else {
                break;
            };

            if !self.handle_input(&input_source, output, error)? {
                break;
            }
        }

        Ok(())
    }

    fn handle_input<W: Write, E: Write>(
        &mut self,
        input_source: &str,
        output: &mut W,
        error: &mut E,
    ) -> io::Result<bool> {
        match ReplCommand::parse(input_source) {
            ReplCommand::Empty => {}
            ReplCommand::Help => self.print_help(output)?,
            ReplCommand::Quit => return Ok(false),
            ReplCommand::Reset => {
                self.session.clear();
                writeln!(output, "session reset")?;
            }
            ReplCommand::Type(source) => {
                let result = self.session.type_of(source);
                self.print_result(result, output, error)?;
            }
            ReplCommand::Unknown(command) => {
                writeln!(error, "unknown command: {command}")?;
            }
            ReplCommand::Evaluate(source) => {
                let result = self.session.eval(source);
                self.print_result(result, output, error)?;
            }
        }

        Ok(true)
    }

    fn read_input<R: BufRead, W: Write>(
        &self,
        input: &mut R,
        output: &mut W,
    ) -> io::Result<Option<String>> {
        let mut buffer = String::new();
        let mut is_first_line = true;

        loop {
            if is_first_line {
                output.write_all(PRIMARY_PROMPT)?;
            } else {
                output.write_all(CONTINUATION_PROMPT)?;
            }
            output.flush()?;

            let mut line = String::new();
            let bytes_read = input.read_line(&mut line)?;
            if bytes_read == 0 {
                if buffer.trim().is_empty() {
                    return Ok(None);
                }

                return Ok(Some(buffer));
            }

            if is_first_line && ReplCommand::is_command_input(&line) {
                return Ok(Some(line));
            }

            buffer.push_str(&line);
            if buffer.trim().is_empty() || !crate::repl::needs_more_input(&buffer) {
                return Ok(Some(buffer));
            }

            is_first_line = false;
        }
    }

    fn print_help<W: Write>(&self, output: &mut W) -> io::Result<()> {
        output.write_all(
            b"commands:\n  /help         show this help\n  /quit         exit\n  exit, quit    exit\n  /reset        clear the session\n  /type <expr>  print the inferred type\n",
        )
    }

    fn print_result<W: Write, E: Write>(
        &self,
        result: ReplEvalResult,
        output: &mut W,
        error: &mut E,
    ) -> io::Result<()> {
        match result {
            ReplEvalResult::Output {
                stdout,
                stderr,
                value,
            } => {
                output.write_all(stdout.as_bytes())?;
                error.write_all(stderr.as_bytes())?;
                if let Some(value) = value {
                    writeln!(output, "{value}")?;
                }
            }
            ReplEvalResult::Diagnostics {
                source,
                diagnostics,
                message,
            } => {
                for diagnostic in diagnostics {
                    error.write_all(
                        render_text(
                            crate::repl::REPL_DOCUMENT_ID,
                            &source,
                            &diagnostic,
                            ColorMode::Auto,
                        )
                        .as_bytes(),
                    )?;
                }
                if let Some(message) = message {
                    error.write_all(message.as_bytes())?;
                }
            }
            ReplEvalResult::Error(message) => {
                writeln!(error, "error: {message}")?;
            }
        }

        Ok(())
    }
}

struct ReplHelper {
    session: ReplSession,
    use_color: bool,
}

impl ReplHelper {
    fn new(session: &ReplSession, use_color: bool) -> Self {
        Self {
            session: session.clone(),
            use_color,
        }
    }

    fn set_session(&mut self, session: &ReplSession, use_color: bool) {
        self.session = session.clone();
        self.use_color = use_color;
    }

    fn complete_source(
        &self,
        line: &str,
        pos: usize,
        original_line_offset: usize,
    ) -> rustyline::Result<(usize, Vec<Pair>)> {
        let completions = self
            .session
            .complete_source(line, pos, original_line_offset);
        let candidates = completions
            .items
            .into_iter()
            .map(|item| Pair {
                display: item.display,
                replacement: item.replacement,
            })
            .collect();
        Ok((completions.start, candidates))
    }

    fn complete_command(&self, line: &str, pos: usize) -> rustyline::Result<(usize, Vec<Pair>)> {
        let prefix = &line[..pos.min(line.len())];
        let commands = ["/help", "/quit", "/reset", "/type"];
        let candidates = commands
            .into_iter()
            .filter(|command| command.starts_with(prefix))
            .map(|command| Pair {
                display: command.to_string(),
                replacement: if command == "/type" {
                    "/type ".to_string()
                } else {
                    command.to_string()
                },
            })
            .collect();

        Ok((0, candidates))
    }

    fn highlight_repl_command(&self, line: &str) -> Option<String> {
        if let Some(expr) = line.strip_prefix("/type ") {
            return Some(format!(
                "\x1b[1;36m/type\x1b[0m {}",
                self.highlight_line(expr)
            ));
        }

        if line.starts_with('/') {
            let command_end = line.find(char::is_whitespace).unwrap_or(line.len());
            let mut highlighted = String::new();
            highlighted.push_str("\x1b[1;36m");
            highlighted.push_str(&line[..command_end]);
            highlighted.push_str("\x1b[0m");
            highlighted.push_str(&line[command_end..]);
            return Some(highlighted);
        }

        if line == "exit" || line == "quit" {
            return Some(format!("\x1b[1;36m{line}\x1b[0m"));
        }

        None
    }

    fn highlight_line(&self, line: &str) -> String {
        let mut tokens = TalkHighlighter::new(line).highlight();
        tokens.sort_by_key(|token| (token.start, token.end));

        let mut highlighted = String::new();
        let mut cursor = 0usize;
        for token in tokens {
            let start = token.start as usize;
            let end = token.end as usize;
            if start < cursor || start >= end || end > line.len() {
                continue;
            }
            if !line.is_char_boundary(start) || !line.is_char_boundary(end) {
                continue;
            }

            highlighted.push_str(&line[cursor..start]);
            highlighted.push_str(style_for_highlight(token.kind));
            highlighted.push_str(&line[start..end]);
            highlighted.push_str("\x1b[0m");
            cursor = end;
        }
        highlighted.push_str(&line[cursor..]);
        highlighted
    }
}

impl Helper for ReplHelper {}

impl Completer for ReplHelper {
    type Candidate = Pair;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        _ctx: &rustyline::Context<'_>,
    ) -> rustyline::Result<(usize, Vec<Self::Candidate>)> {
        let pos = pos.min(line.len());
        if line.starts_with("/type ") && pos >= "/type ".len() {
            return self.complete_source(
                &line["/type ".len()..],
                pos - "/type ".len(),
                "/type ".len(),
            );
        }
        if line.starts_with('/') {
            return self.complete_command(line, pos);
        }

        self.complete_source(line, pos, 0)
    }
}

impl Hinter for ReplHelper {
    type Hint = String;
}

impl Highlighter for ReplHelper {
    fn highlight<'l>(&self, line: &'l str, _pos: usize) -> Cow<'l, str> {
        if !self.use_color {
            return Cow::Borrowed(line);
        }

        if let Some(highlighted) = self.highlight_repl_command(line) {
            return Cow::Owned(highlighted);
        }

        Cow::Owned(self.highlight_line(line))
    }

    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(
        &'s self,
        prompt: &'p str,
        default: bool,
    ) -> Cow<'b, str> {
        if !default || !self.use_color {
            return Cow::Borrowed(prompt);
        }

        Cow::Owned(format!("\x1b[1;36m{prompt}\x1b[0m"))
    }

    fn highlight_candidate<'c>(
        &self,
        candidate: &'c str,
        _completion: CompletionType,
    ) -> Cow<'c, str> {
        if !self.use_color {
            return Cow::Borrowed(candidate);
        }

        Cow::Owned(format!("\x1b[1;33m{candidate}\x1b[0m"))
    }

    fn highlight_char(&self, _line: &str, _pos: usize, _kind: CmdKind) -> bool {
        self.use_color
    }
}

impl Validator for ReplHelper {
    fn validate(&self, ctx: &mut ValidationContext<'_>) -> rustyline::Result<ValidationResult> {
        let input = ctx.input();
        if input.trim().is_empty() || ReplCommand::is_command_input(input) {
            return Ok(ValidationResult::Valid(None));
        }

        if self.session.needs_more_input(input) {
            return Ok(ValidationResult::Incomplete);
        }

        Ok(ValidationResult::Valid(None))
    }
}

fn terminal_color_enabled() -> bool {
    io::stdout().is_terminal() && std::env::var_os("NO_COLOR").is_none()
}

fn history_path() -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("TALK_HISTORY_FILE") {
        let path = PathBuf::from(path);
        create_history_parent(&path);
        return Some(path);
    }

    let home = std::env::var_os("HOME").or_else(|| std::env::var_os("USERPROFILE"))?;
    let path = PathBuf::from(home).join(HISTORY_FILE_NAME);
    create_history_parent(&path);
    Some(path)
}

fn create_history_parent(path: &std::path::Path) {
    let Some(parent) = path.parent() else {
        return;
    };
    if parent.as_os_str().is_empty() {
        return;
    }
    let _ = std::fs::create_dir_all(parent);
}

fn readline_to_io_error(err: ReadlineError) -> io::Error {
    io::Error::other(err.to_string())
}

fn style_for_highlight(kind: HighlightKind) -> &'static str {
    match kind {
        HighlightKind::KEYWORD | HighlightKind::MODIFIER => "\x1b[1;35m",
        HighlightKind::STRING => "\x1b[32m",
        HighlightKind::NUMBER => "\x1b[36m",
        HighlightKind::COMMENT => "\x1b[2;90m",
        HighlightKind::TYPE
        | HighlightKind::CLASS
        | HighlightKind::ENUM
        | HighlightKind::INTERFACE
        | HighlightKind::STRUCT
        | HighlightKind::TYPE_PARAMETER => "\x1b[1;34m",
        HighlightKind::FUNCTION | HighlightKind::METHOD => "\x1b[1;33m",
        HighlightKind::PARAMETER | HighlightKind::VARIABLE | HighlightKind::PROPERTY => {
            "\x1b[1;37m"
        }
        HighlightKind::ENUM_MEMBER => "\x1b[33m",
        HighlightKind::OPERATOR | HighlightKind::EFFECT => "\x1b[35m",
        HighlightKind::DECORATOR | HighlightKind::MACRO => "\x1b[35m",
        HighlightKind::NAMESPACE | HighlightKind::EVENT | HighlightKind::REGEXP => "\x1b[0m",
    }
}

enum ReplCommand<'a> {
    Empty,
    Help,
    Quit,
    Reset,
    Type(&'a str),
    Unknown(String),
    Evaluate(&'a str),
}

impl<'a> ReplCommand<'a> {
    fn is_command_input(input: &str) -> bool {
        let trimmed = input.trim();
        trimmed.starts_with('/')
            || trimmed.starts_with(':')
            || trimmed == "exit"
            || trimmed == "quit"
    }

    fn parse(input: &'a str) -> Self {
        let trimmed = input.trim();
        if trimmed.is_empty() {
            return Self::Empty;
        }

        match trimmed {
            "exit" | "quit" | "/quit" => return Self::Quit,
            "/help" => return Self::Help,
            "/reset" => return Self::Reset,
            _ => {}
        }

        if let Some(source) = trimmed.strip_prefix("/type") {
            return Self::Type(source.trim());
        }

        if trimmed.starts_with('/') {
            return Self::Unknown(trimmed.to_string());
        }

        if trimmed.starts_with(':') {
            return Self::Unknown(format!("{trimmed} (commands use /, not :)"));
        }

        Self::Evaluate(input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn session() -> ReplSession {
        ReplSession::with_source_path(PathBuf::from("repl.tlk"))
    }

    #[test]
    fn slash_commands_complete() {
        let session = session();
        let helper = ReplHelper::new(&session, false);
        let history = DefaultHistory::new();
        let ctx = rustyline::Context::new(&history);
        let (start, candidates) = helper.complete("/h", 2, &ctx).unwrap();
        assert_eq!(start, 0);
        assert!(
            candidates
                .iter()
                .any(|candidate| candidate.replacement == "/help")
        );
    }

    #[test]
    fn semantic_completion_uses_persisted_declarations() {
        let mut session = session();
        let result = session.eval("let longName = 2");
        assert!(matches!(result, ReplEvalResult::Output { value: None, .. }));

        let helper = ReplHelper::new(&session, false);
        let history = DefaultHistory::new();
        let ctx = rustyline::Context::new(&history);
        let (_start, candidates) = helper.complete("long", 4, &ctx).unwrap();
        assert!(
            candidates
                .iter()
                .any(|candidate| candidate.replacement == "longName")
        );
    }
}
