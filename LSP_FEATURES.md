# Talk Language Server Protocol (LSP) Features

This document summarizes the LSP features implemented for the Talk programming language.

## Implemented Features

### 1. Go to Definition
- Navigate to the definition of symbols (functions, types, variables, properties, methods)
- Works with array methods like `push`, `get`, `pop`
- Supports navigation to prelude/core library definitions

### 2. Hover Information
- Shows type information when hovering over symbols
- Displays symbol kind (function, struct, enum, etc.)
- Shows definition location
- Support for documentation (when available)

### 3. Document Symbols (Outline View)
- Lists all symbols in a document
- Supports functions, structs, enums, protocols, properties, and more
- Symbols are sorted by position in the file

### 4. Document Highlighting
- Highlights all occurrences of a symbol in the current file
- Useful for seeing where a variable/function is used

### 5. Rename Symbol
- Rename symbols across all files in the workspace
- Updates all references to the renamed symbol
- Preserves correct semantics

### 6. Find References
- Find all references to a symbol across the codebase
- Optionally includes the declaration/definition
- Works across multiple files

### 7. Completion
- Context-aware code completion
- Member access completion (properties and methods)
- Triggered by `.` and `:` characters

### 8. Diagnostics
- Real-time error reporting
- Type errors, syntax errors, and semantic errors
- Diagnostics are debounced to avoid overwhelming the user

### 9. Semantic Tokens
- Syntax highlighting based on semantic analysis
- Different colors for different symbol types

### 10. Document Formatting
- Format entire documents according to Talk style guidelines

## Architecture

The LSP implementation uses:
- A semantic index for storing resolved expression information
- Symbol tables with proper symbol IDs for navigation
- Type information from the type checker
- Query-based architecture inspired by rust-analyzer

## Testing

To test the LSP features:
1. Open a Talk file in an LSP-enabled editor (VSCode with Talk extension)
2. Try hovering over symbols to see type information
3. Use Ctrl/Cmd+Click to navigate to definitions
4. Use F2 to rename symbols
5. Use Shift+F12 to find all references
6. Use Ctrl/Cmd+Shift+O to see document outline

## Future Improvements

Potential enhancements:
- Code actions (quick fixes)
- Inlay hints for type annotations
- Call hierarchy
- Type hierarchy
- Workspace symbols
- Code lens for running tests
- Signature help for function calls