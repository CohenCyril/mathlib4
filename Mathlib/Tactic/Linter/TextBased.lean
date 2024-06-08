/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Batteries.Data.String.Basic
import Cli.Basic
import Mathlib.Init.Data.Nat.Notation

/-!
## Text-based linters

This file defines various mathlib linters which are based on reading the source code only.
In practice, only style linters will have this form.
All of these have been rewritten from the `lint-style.py` script.

For now, this only contains the linter for too large files:
further linters will be ported in subsequent PRs.

-/

open System

/-- Possible errors that text-based linters can report. -/
-- We collect these in one inductive type to centralise error reporting.
inductive StyleError where
  /-- The current file was too large: this error contains the current number of lines
  as well as a size limit (slightly larger). On future runs, this linter will allow this file
  to grow up to this limit. -/
  | fileTooLong (number_lines : ℕ) (new_size_limit : ℕ) : StyleError
  deriving BEq

/-- How to format style errors -/
inductive ErrorFormat
  /-- Produce style error output aimed at humans: no error code, clickable file name -/
  | humanReadable : ErrorFormat
  /-- Produce an entry in the style-exceptions file: mention the error code, slightly uglier
  than humand-readable output -/
  | exceptionsFile : ErrorFormat
  /-- Produce output suitable for Github error annotations: in particular,
  duplicate the file path, line number and error code -/
  | github : ErrorFormat

/-- Create the underlying error message for a given `StyleError`. -/
def StyleError.errorMessage (err : StyleError) (style : ErrorFormat) : String := match err with
  | StyleError.fileTooLong current_size size_limit =>
    match style with
    | ErrorFormat.github =>
        s!"file contains {current_size} lines (at most {size_limit} allowed), try to split it up"
    | ErrorFormat.exceptionsFile =>
        s!"{size_limit} file contains {current_size} lines, try to split it up"
    | ErrorFormat.humanReadable => s!"file contains {current_size} lines, try to split it up"

/-- The error code for a given style error. Keep this in sync with `parse?_errorContext` below! -/
-- FUTURE: we're matching the old codes in `lint-style.py` for compatibility;
-- in principle, we could also print something more readable.
def StyleError.errorCode (err : StyleError) : String := match err with
  | StyleError.fileTooLong _ _ => "ERR_NUM_LIN"

/-- Context for a style error: the actual error, the line number in the file we're reading
and the path to the file. -/
structure ErrorContext where
  /-- The underlying `StyleError`-/
  error : StyleError
  /-- The line number of the error -/
  lineNumber : ℕ
  /-- The path to the file which was linted -/
  path : FilePath

/-- The parts of a `StyleError` which are considered when matching against the existing
  style exceptions: for example, we ignore the particular line length of a "line too long" error. -/
def StyleError.normalise (err : StyleError) : StyleError := match err with
  -- NB: keep this in sync with `parse?_errorContext` below.
  | StyleError.fileTooLong _ _ => StyleError.fileTooLong 0 0

/-- Careful: we do not want to compare `ErrorContexts` exactly; we ignore some details. -/
instance : BEq ErrorContext where
  beq ctx ctx' :=
      -- XXX: `lint-style.py` was calling `resolve()` on the path before before comparing them
      -- should we also do so?
      ctx.path == ctx'.path
      -- We completely ignore line numbers of errors. Not sure if this is best.
      -- We normalise errors before comparing them.
      && (ctx.error).normalise == (ctx'.error).normalise

/-- Output the formatted error message, containing its context.

`style` specifies if the error should be formatted for humans or for github output matchers -/
def outputMessage (errctx : ErrorContext) (style : ErrorFormat) : String :=
  let error_message := errctx.error.errorMessage style
  match style with
  | ErrorFormat.github =>
    -- We are outputting for github: duplicate file path, line number and error code,
    -- so that they are also visible in the plain text output.
    let path := errctx.path
    let nr := errctx.lineNumber
    let code := errctx.error.errorCode
    s!"::ERR file={path},line={nr},code={code}::{path}:{nr} {code}: {error_message}"
  | ErrorFormat.humanReadable =>
    -- Print for humans: clickable file name and omit the error code
    s!"error: {errctx.path}:{errctx.lineNumber} {error_message}"
  | ErrorFormat.exceptionsFile =>
    -- Produce an entry in the exceptions file: with error code and "line" in front of the number.
    s!"{errctx.path} : line {errctx.lineNumber} : {errctx.error.errorCode} : {error_message}"

/-- Try parsing an `ErrorContext` from a string: return `some` if successful, `none` otherwise. -/
def parse?_errorContext (line : String) : Option ErrorContext := Id.run do
  let parts := line.split (· == ' ')
  match parts with
    | filename :: ":" :: "line" :: _line_number :: ":" :: error_code :: ":" :: error_message =>
      -- Turn the filename into a path. In general, this is ambiguous if we don't know if we're
      -- dealing with e.g. Windows or POSIX paths. In our setting, this is fine, since no path
      -- component contains any path separator.
      let path := mkFilePath (filename.split (FilePath.pathSeparators.contains ·))
      -- Parse the error kind from the error code, ugh.
      -- NB: keep this in sync with `StyleError.errorCode` above!
      let err : Option StyleError := match error_code with
        -- Use default values for parameters which are normalised.
        -- NB: keep this in sync with `normalise` above!
        | "ERR_NUM_LIN" =>
          -- Parse the error message in the script. `none` indicates invalid input.
          match (error_message.get? 0, error_message.get? 3) with
          | (some limit, some current) =>
            match (String.toNat? limit, String.toNat? current) with
            | (some size_limit, some current_size) =>
              some (StyleError.fileTooLong current_size size_limit)
            | _ => none
          | _ => none
        | _ => none
      -- Omit the line number, as we don't use it anyway.
      return (err.map fun e ↦ (ErrorContext.mk e 0 path))
    -- XXX: print an error on any lines which don't match the particular format.
    | _ => -- IO.println s!"Invalid input file: line {line} doesn't match any particular format"
      none

/-- Parse all style exceptions for a line of input.
Return an array of all exceptions which could be parsed: invalid input is ignored. -/
def parseStyleExceptions (lines : Array String) : Array ErrorContext := Id.run do
  -- We treat all lines starting with "--" as a comment and ignore them.
  Array.filterMap (parse?_errorContext ·) (lines.filter (fun line ↦ !line.startsWith "--"))

/-- Print information about all errors encountered to standard output.

`style` specifies if we print errors for humand or github consumption. -/
def formatErrors (errors : Array ErrorContext) (style : ErrorFormat) : IO Unit := do
  for e in errors do
    IO.println (outputMessage e style)

/-- Core logic of a text based linter: given a collection of lines,
return an array of all style errors with line numbers. -/
abbrev TextbasedLinter := Array String → Array (StyleError × ℕ)

/-! Definitions of the actual text-based linters. -/
section

/-- Whether a collection of lines consists *only* of imports, blank lines and single-line comments.
In practice, this means it's an imports-only file and exempt from almost all linting. -/
def isImportsOnlyFile (lines : Array String) : Bool :=
  -- The Python version also excluded multi-line comments: for all files generated by `mk_all`,
  -- this is in fact not necessary.
  lines.all (fun line ↦ line.startsWith "import " || line == "" || line.startsWith "-- ")

/-- Error if a collection of lines is too large. "Too large" means more than 1500 lines
**and** longer than an optional previous limit.
If the file is too large, return a matching `StyleError`, which includes a new size limit
(which is somewhat larger than the current size). -/
def checkFileLength (lines : Array String) (existing_limit : Option ℕ) : Option StyleError :=
  Id.run do
  if lines.size > 1500 then
    let is_larger : Bool := match existing_limit with
    | some mark => lines.size > mark
    | none => true
    if is_larger then
      -- We add about 200 lines of slack to the current file size:
      -- small PRs will be unperturbed, but sufficiently large PRs will get nudged towards
      -- splitting up this file.
      return some (StyleError.fileTooLong lines.size ((Nat.div lines.size 100) * 100 + 200))
  none

end

/-- All text-based linters registered in this file. -/
def allLinters : Array TextbasedLinter := Array.mk
  []

/-- Controls what kind of output this programme produces. -/
inductive OutputSetting : Type
  /-- Print any style error to standard output (the default) -/
  | print (style : ErrorFormat)
  /-- Append all new errors to the style exceptions file (and print them?),
  leaving existing ones intact -/
  | append
  /-- Regenerate the whole style exceptions file -/
  | regenerate

/-- Append a given string at the end of an existing file. -/
-- XXX: move this to `Init.System.IO.lean` in Lean core
def IO.FS.appendToFile (fname : System.FilePath) (content : String) : IO Unit := do
  let previous_content ← IO.FS.readFile fname
  IO.FS.writeFile fname (previous_content ++ content)

/-- Read a file and apply all text-based linters.
Print formatted errors and possibly update the style exceptions file accordingly.

Return `true` if there were new errors (and `false` otherwise).
`sizeLimit` is any pre-existing limit on this file's size.
`mode` specifies what kind of output this script should produce. -/
def lintFile (path : FilePath) (sizeLimit : Option ℕ) (mode : OutputSetting) : IO Bool := do
  let lines ← IO.FS.lines path
  -- We don't need to run any checks on imports-only files.
  -- NB. The Python script used to still run a few linters; this is in fact not necessary.
  if isImportsOnlyFile lines then
    return false
  if let some (StyleError.fileTooLong n limit) := checkFileLength lines sizeLimit then
    let err := ErrorContext.mk (StyleError.fileTooLong n limit) 1 path
    match mode with
    | OutputSetting.print style => formatErrors (Array.mkArray1 err) style
    -- XXX: should these also print the errors? if yes, only for humans, I guess!
    | OutputSetting.append =>
      let path := System.mkFilePath ["scripts/style-exceptions.txt"]
      IO.FS.appendToFile path (s!"{outputMessage err ErrorFormat.exceptionsFile}\n")
    | OutputSetting.regenerate =>
    -- FIXME: implement this!
      IO.println "the --regenerate option is not implemented yet: \
        please call `./scripts/update-style-exceptions.sh instead"
    return true
  return false

/-- Lint a list of files referenced and return the number of files which had new style errors.
`mode` specifies what kind of output this script should produce. -/
def lintFiles (files : Array System.FilePath) (mode : OutputSetting) : IO UInt32 := do
  -- Read the style exceptions file.
  let exceptions_file ← IO.FS.lines (mkFilePath ["scripts/style-exceptions.txt"])
  let style_exceptions := parseStyleExceptions exceptions_file
  let mut number_error_files := 0
  for file in files do
    -- Find the size limit for this given file.
    -- If several size limits are given (unlikely in practice), we use the first one.
    let size_limits := (style_exceptions.filter (·.path == file)).filterMap (fun errctx ↦
      match errctx.error with
      | StyleError.fileTooLong _ limit => some limit)
    if ← lintFile file (size_limits.get? 0) mode then
      number_error_files := number_error_files + 1
  return number_error_files

/-- Lint all files referenced in a given import-only file.
Return the number of files which had new style errors.
`mode` specifies what kind of output this script should produce. -/
def lintAllFiles (path : System.FilePath) (mode : OutputSetting) : IO UInt32 := do
  -- Read all module names from the file at `path` and convert to file paths.
  let allModules ← IO.FS.lines path
  let paths := allModules.map (fun mod ↦
    (System.mkFilePath ((mod.stripPrefix "import ").split fun c ↦ (c == '.'))).addExtension "lean"
  )
  let n ← lintFiles paths mode
  if n > 0 && mode matches OutputSetting.print _ then
    IO.println "run with the --update flag to add all style errors to the style exceptions file"
  return n

open Cli in
/-- Implementation of the `lint_style` command line program. -/
def lintStyleCli (args : Cli.Parsed) : IO UInt32 := do
  if args.hasFlag "update" && args.hasFlag "regenerate" then
    IO.println "invalid options: the --update and --regenerate flags are mutually exclusive"
    return 2
  if args.variableArgs.size > 0 && args.hasFlag "regenerate" then
    IO.println "invalid options: the --regenerate flag can only be used when linting all files"
  let errorStyle := if args.hasFlag "github" then ErrorFormat.github else ErrorFormat.humanReadable
  let mode : OutputSetting := match (args.hasFlag "update", args.hasFlag "regenerate") with
  | (true, false) => OutputSetting.append
  | (false, true) => OutputSetting.regenerate
  | (false, false) | (true, true) => OutputSetting.print errorStyle
  let mut number_error_files : UInt32 := 0
  let files := args.variableArgsAs! String
  if files.size > 0 then
    -- Only lint the specified files.
    for filename in files do
      if !(← System.FilePath.pathExists filename) then
        IO.println s!"invalid input: file {filename} does not exist"
        return 2
    let paths := files.map (fun fname ↦ System.mkFilePath [fname])
    number_error_files := number_error_files + (← lintFiles paths mode)
  else
    for s in ["Archive.lean", "Counterexamples.lean", "Mathlib.lean"] do
        let n ← lintAllFiles (mkFilePath [s]) mode
        number_error_files := number_error_files + n
  return number_error_files

open Cli in
/-- Setting up command line options and help text for `lake exe lint_style`. -/
-- so far, no help options or so: perhaps that is fine?
def lint_style : Cmd := `[Cli|
  lint_style VIA lintStyleCli; ["0.0.1"]
  "Run text-based style linters on every Lean file in Mathlib/, Archive/ and Counterexamples/."

  FLAGS:
    github;     "Print errors in a format suitable for github problem matchers\
                 otherwise, produce human-readable output"
    update;     "Append all new errors to the current list of exceptions \
                 (leaving existing entries untouched)"
    regenerate; "(not implemented yet) Fully regenerate the file of style exceptions: \
                 this may update or remove existing entries"

  ARGS:
    ...files : String; "Only lint these file(s)"
]

/-- The entry point to the `lake exe lint_style` command. -/
def main (args : List String) : IO UInt32 := lint_style.validate args
