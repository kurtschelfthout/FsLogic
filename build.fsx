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
let testAssemblies = "tests/**/bin/Release/*Test*.dll"
let gitOwner = "kurtschelfthout"
let gitHome = "https://github.com/" + gitOwner
let gitName = "FsLogic"
let gitRaw = environVarOrDefault "gitRaw" ("https://raw.githubusercontent.com/" + gitOwner)
let netFrameworks = ["v4.6"]
let buildDir = "bin"

Target "Build"( fun _ ->
    netFrameworks
    |> List.iter( fun framework ->
        let outputPath = buildDir </> framework
        !! (project + ".sln")
        |> MSBuild outputPath "Build" ["Configuration","Release"; "TargetFrameworkVersion", framework]
        |> Log (".NET " + framework + " Build-Output: "))
)

Target "Clean"( fun _ ->
    CleanDirs [buildDir]
)

RunTargetOrDefault "Build"
