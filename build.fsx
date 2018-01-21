#r @"packages/Fake/tools/Fakelib.dll"
open Fake

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
let testFolder = "FsLogic.Test"
let gitOwner = "kurtschelfthout"
let gitHome = "https://github.com/" + gitOwner
let gitName = "FsLogic"
let gitRaw = environVarOrDefault "gitRaw" ("https://raw.githubusercontent.com/" + gitOwner)


Target "Build" (fun _ ->
    DotNetCli.Build (fun p -> { p with Configuration = "Release" })
)

Target "Test" (fun _ -> 
    DotNetCli.RunCommand (fun p ->  { p with WorkingDir = testFolder }) "run"
)

//Target "Clean"( fun _ ->
//    CleanDirs [buildDir]
//)

"Build"
==> "Test"

RunTargetOrDefault "Test"
