[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path $PSScriptRoot -Parent
. (Join-Path $PSScriptRoot 'Enter-Lean.ps1')

function Invoke-Checked {
    param([string] $Program, [string[]] $Arguments)
    & $Program @Arguments
    if ($LASTEXITCODE -ne 0) {
        throw "$Program failed with exit code $LASTEXITCODE."
    }
}

Push-Location $projectRoot
try {
    if (-not (Get-Command git -ErrorAction SilentlyContinue)) {
        throw 'Git for Windows is required. Install Git and run this script again.'
    }
    $elanExe = Join-Path $env:ELAN_HOME 'bin\elan.exe'
    if (-not (Test-Path -LiteralPath $elanExe)) {
        $downloadDir = Join-Path $projectRoot '.tools\downloads'
        $null = New-Item -ItemType Directory -Path $downloadDir -Force
        $archive = Join-Path $downloadDir 'elan-windows.zip'
        $url = 'https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-pc-windows-msvc.zip'
        Write-Host "Downloading Elan from $url"
        Invoke-WebRequest -UseBasicParsing -Uri $url -OutFile $archive -TimeoutSec 120
        Expand-Archive -LiteralPath $archive -DestinationPath $downloadDir -Force
        Invoke-Checked -Program (Join-Path $downloadDir 'elan-init.exe') -Arguments @(
            '-y', '--no-modify-path', '--default-toolchain', 'none'
        )
    }

    $toolchain = (Get-Content -Raw -LiteralPath 'lean-toolchain').Trim()
    Invoke-Checked -Program $elanExe -Arguments @('toolchain', 'install', $toolchain)
    Invoke-Checked -Program (Join-Path $env:ELAN_HOME 'bin\lean.exe') -Arguments @('--version')
    if (-not (Test-Path -LiteralPath '.git')) {
        Invoke-Checked -Program 'git' -Arguments @('init')
    }
    $lakeExe = Join-Path $env:ELAN_HOME 'bin\lake.exe'
    # mathlib's post-update hook downloads its cache automatically.
    # A saved manifest preserves the resolved dependency commits on later runs.
    if (-not (Test-Path -LiteralPath 'lake-manifest.json')) {
        Invoke-Checked -Program $lakeExe -Arguments @('update')
    }
    Invoke-Checked -Program $lakeExe -Arguments @('exe', 'cache', 'get')
    Invoke-Checked -Program $lakeExe -Arguments @('build')
    Write-Host 'Lean, mathlib, and the Chipping baseline built successfully.'
} finally {
    Pop-Location
}
