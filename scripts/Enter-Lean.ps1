# Dot-source this file: . .\scripts\Enter-Lean.ps1
$env:ELAN_HOME = Join-Path (Split-Path $PSScriptRoot -Parent) '.tools\elan'
$leanBin = Join-Path $env:ELAN_HOME 'bin'
if (($env:PATH -split ';') -notcontains $leanBin) {
    $env:PATH = "$leanBin;$env:PATH"
}
