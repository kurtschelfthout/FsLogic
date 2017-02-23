#r @"packages/Fake/tools/Fakelib.dll"
open Fake
open Fake.Testing.Expecto

// --------------------------------------------------------------------------
// Project Configuration Information used in NuGet and AssemblyInfo Targets
// --------------------------------------------------------------------------

let project = "FsLogic"
let authors = ["Kurt Schelfthout"]
let summary = "A library for logic programming in F#"
let description = """
    A library for logic programming in F#.
    """
let tags = "fsharp logic-programming relational-programming"
let testAssembly = "FsLogic.Test.exe"
let gitOwner = "kurtschelfthout"
let gitHome = "https://github.com/" + gitOwner
let gitName = "FsLogic"
let gitRaw = environVarOrDefault "gitRaw" ("https://raw.githubusercontent.com/" + gitOwner)
let buildDir = "bin"

Target "Build" (fun _ ->
        !! (project + ".sln")
        |> MSBuild buildDir "Build" ["Configuration","Release"]
        |> Log (" Build-Output: ")
)

Target "Test" (fun _ ->
  Expecto id (Seq.singleton (buildDir </> testAssembly))
)

Target "Clean"( fun _ ->
    CleanDirs [buildDir]
)

"Clean"
==> "Build"
==> "Test"

RunTargetOrDefault "Test"
