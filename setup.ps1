# Reproducible standalone Windows setup; all downloaded files remain in lean/.
$ErrorActionPreference = 'Stop'
$toolchain = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'toolchain-windows.json') -Raw | ConvertFrom-Json
$toolchainSpec = (Get-Content -LiteralPath (Join-Path $PSScriptRoot 'lean-toolchain') -Raw).Trim()
if ($toolchainSpec -ne "leanprover/lean4:v$($toolchain.version)") {
    throw 'Toolchain specification and Windows download manifest disagree.'
}
$toolsDir = Join-Path $PSScriptRoot '.tools'
$archive = Join-Path $toolsDir $toolchain.archive
$leanExe = Join-Path $toolsDir "lean-$($toolchain.version)-windows/bin/lean.exe"
New-Item -ItemType Directory -Path $toolsDir -Force | Out-Null
if (-not (Test-Path -LiteralPath $leanExe)) {
    if (-not (Test-Path -LiteralPath $archive)) {
        & curl.exe -L --fail --retry 3 --silent --show-error -o $archive $toolchain.url
        if ($LASTEXITCODE -ne 0) { throw 'Lean download failed.' }
    }
    if ((Get-FileHash -LiteralPath $archive -Algorithm SHA256).Hash.ToLowerInvariant() -ne $toolchain.sha256) {
        throw 'Lean archive checksum mismatch.'
    }
    & tar.exe -xf $archive -C $toolsDir
    if ($LASTEXITCODE -ne 0) { throw 'Lean extraction failed.' }
}
& $leanExe --version
if ($LASTEXITCODE -ne 0) { throw 'Lean version check failed.' }
$savedNoCache = $env:MATHLIB_NO_CACHE_ON_UPDATE
try {
    $env:MATHLIB_NO_CACHE_ON_UPDATE = '1'
    $manifestPath = Join-Path $PSScriptRoot 'lake-manifest.json'
    $needsUpdate = -not (Test-Path -LiteralPath $manifestPath)
    if (-not $needsUpdate) {
        $manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json
        $mathlib = @($manifest.packages | Where-Object { $_.name -eq 'mathlib' })
        $specht = @($manifest.packages | Where-Object { $_.name -eq 'RepresentationTheoryFormalization' })
        $needsUpdate = $mathlib.Count -ne 1 -or $mathlib[0].rev -ne $toolchain.mathlibRevision -or
            $specht.Count -ne 1 -or $specht[0].type -ne 'path' -or
            $specht[0].dir -ne 'vendor/etingof-representation-theory'
    }
    if ($needsUpdate) {
        & (Join-Path $PSScriptRoot 'lake-local.ps1') update
        if ($LASTEXITCODE -ne 0) { throw 'Lake dependency update failed.' }
    }
    # The selected representation-theory modules import the full Mathlib umbrella.
    & (Join-Path $PSScriptRoot 'lake-local.ps1') exe cache get --cache-from=legacy Mathlib
    if ($LASTEXITCODE -ne 0) { throw 'Mathlib cache fetch failed.' }
} finally { $env:MATHLIB_NO_CACHE_ON_UPDATE = $savedNoCache }
& (Join-Path $PSScriptRoot 'lake-local.ps1') build
if ($LASTEXITCODE -ne 0) { throw 'Lake build failed.' }
