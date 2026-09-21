# Invoke from any directory using the exact local toolchain selected by the project.
# Package artifact downloads are disabled; setup.ps1 fetches the mathlib cache explicitly.
$ErrorActionPreference = 'Stop'
$toolchainSpec = (Get-Content -LiteralPath (Join-Path $PSScriptRoot 'lean-toolchain') -Raw).Trim()
if ($toolchainSpec -notmatch '^leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+(?:-[0-9A-Za-z.-]+)?)$') {
    throw "Unsupported local toolchain specification: $toolchainSpec"
}
$toolchainVersion = $Matches[1]
$leanBin = Join-Path $PSScriptRoot ".tools/lean-$toolchainVersion-windows/bin"
if (-not (Test-Path -LiteralPath (Join-Path $leanBin 'lake.exe'))) {
    throw "Local Lean $toolchainVersion is not installed. Run setup.ps1."
}
$savedPath = $env:PATH
$savedCache = $env:MATHLIB_CACHE_DIR
try {
    $env:PATH = "$leanBin;$savedPath"
    $env:MATHLIB_CACHE_DIR = Join-Path $PSScriptRoot '.cache/mathlib'
    Push-Location -LiteralPath $PSScriptRoot
    try {
        & (Join-Path $leanBin 'lake.exe') --no-cache @args
        $lakeExit = $LASTEXITCODE
    } finally { Pop-Location }
} finally {
    $env:PATH = $savedPath
    $env:MATHLIB_CACHE_DIR = $savedCache
}
exit $lakeExit
