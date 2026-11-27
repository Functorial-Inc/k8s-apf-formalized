import Lake
open Lake DSL System

require veil from git "https://github.com/verse-lab/veil.git" @ "v4.35.0"

package apfQueueSet where

@[default_target]
lean_lib ApfQueueSet where
  globs := #[.submodules `ApfQueueSet]

lean_exe tracecheck where
  root := `ApfQueueSet.TraceCheckMain

lean_exe gofix where
  root := `ApfQueueSet.GoFixMain

/-! The script below is copied verbatim from Veil v4.35.0's `lakefile.lean`.
`#model_check` (default and `compiled` modes) runs
`lake script run veilModelCheckBuild` in the root workspace to compile the
model checker it emits, so a downstream project must define it. -/
/-- Compile C emitted by Veil's execution commands using this workspace's native dependencies. -/
script veilModelCheckBuild args do
  let [sourceFile, buildDir] := args
    | throw <| IO.userError "usage: lake script run veilModelCheckBuild <source.lean> <build-directory>"
  let buildDir : FilePath := buildDir
  let ws ← getWorkspace
  let lean ← getLeanInstall
  let imports ← IO.ofExcept <| (← IO.FS.readFile (buildDir / "imports.json"))
    |> Lean.Json.parse |>.bind (Lean.fromJson? (α := Array Lean.Name))
  let sourceMod? := ws.findModuleBySrc? (FilePath.mk sourceFile |>.normalize)
  let pkg := sourceMod?.map (·.pkg) |>.getD ws.root
  let leanConfig : LeanConfig := sourceMod?.map (·.lib.config.toLeanConfig) |>.getD default
  let exeConfig : LeanExeConfig `ModelCheckerMain := {
    toLeanConfig := { leanConfig with buildType := .relWithDebInfo }
  }
  let exe : LeanExe := ⟨pkg, `ModelCheckerMain, exeConfig⟩
  let mut mods := #[]
  for name in imports do
    if let some mod := ws.findModule? name then
      mods := mods.push mod
    else unless ← (Lean.modToFilePath lean.leanLibDir name "olean").pathExists do
      throw <| IO.userError s!"cannot find a Lake module or toolchain library for '{name}'"
  let mut libs := mods.foldl (fun acc mod => acc.insert mod.lib) OrdHashSet.empty
  if let some mod := sourceMod? then
    libs := libs.insert mod.lib
  let _ ← ws.runBuild <| withRegisterJob s!"model-check:{buildDir.fileName.getD "ModelCheckerMain"}" do
    -- The emitted C uses an already elaborated environment. Re-elaborating an import
    -- here could change its definitions or run a nested check under our build lock.
    -- Fetch and await Lean artifacts without rebuilding, in the same job store used
    -- below, so native facets reuse these checked jobs rather than scheduling them again.
    let importTraces ← mods.mapM fun mod =>
      return (← (IO.FS.readFile mod.traceFile).toBaseIO).toOption
    for (mod, previousTrace) in mods.zip importTraces do
      let checked ← withTheReader BuildContext (fun ctx => { ctx with noBuild := true })
        mod.leanArts.fetch
      unless (← checked.wait?).isSome do
        error s!"Imported Lean artifacts for '{mod.name}' need rebuilding. Run `lake build +{mod.name}` \
          in this workspace, then reload the importing file before compiling this check."
      -- `noBuild` may still restore cached artifacts. Do not link a different imported
      -- version into C emitted before that restoration.
      unless (← (IO.FS.readFile mod.traceFile).toBaseIO).toOption == previousTrace do
        error s!"Imported Lean artifacts for '{mod.name}' changed during validation. \
          Reload the importing file before compiling this check."
    let c ← inputTextFile (buildDir / "ModelCheckerMain.c")
    -- Lake v4.35 dropped the include-dir argument of `buildLeanO`; the internal variant
    -- falls back to the toolchain's include directory, as `Module.leanIncludeDir?` did.
    let obj ← Internal.buildLeanO (buildDir / "ModelCheckerMain.o") c
      exe.root.weakLeancArgs exe.root.leancArgs
    let mut objs := #[obj]
    let mut dynlibs := #[]
    -- Mirrors the link-input collection in `LeanExe.recBuildExe`, which cannot be reused
    -- directly: it builds the root module's object from the root's `.lean` source and reads
    -- the root's imports from that source, whereas here the root is C emitted from the
    -- elaborator's environment and the imports come from `imports.json`. It also links into
    -- the package's shared `binDir`, where concurrent checks would overwrite each other.
    -- Lake does not expose the collection on its own, so keep this in sync with
    -- `recBuildExe` when updating the toolchain.
    for mod in mods do
      for facet in mod.nativeFacets exe.supportInterpreter do
        objs := objs.push (← facet.fetch mod)
    for lib in libs.toArray do
      for obj in lib.moreLinkObjs do
        objs := objs.push (← obj.fetchIn lib.pkg)
      for dynlib in lib.moreLinkLibs do
        dynlibs := dynlibs.push (← dynlib.fetchIn lib.pkg)
    -- Compile-time packages (in particular the SMT solver) are not native dependencies.
    let nativePkgs := libs.toArray.foldl (fun acc lib => acc.insert lib.pkg) OrdHashSet.empty
    for dep in nativePkgs.toArray do
      for lib in dep.externLibs do
        objs := objs.push (← lib.static.fetch)
    -- Library link inputs include package inputs, so different libraries can resolve
    -- to the same object. Collect first to retain every dependency's build trace.
    (Job.collectArray objs).bindM (sync := true) fun paths => do
      let mut seen : Std.HashSet FilePath := {}
      let mut unique := #[]
      for path in paths do
        let canonical ← IO.FS.realPath path
        unless seen.contains canonical do
          seen := seen.insert canonical
          unique := unique.push (Job.pure path)
      buildLeanExe (buildDir / exe.fileName) unique dynlibs
        exe.weakLinkArgs exe.linkArgs exe.sharedLean
  return 0
