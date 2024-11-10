---
layout: post
title: "Good bye, Crowded-Up Laundries: Building chart database for AstroDX"
date: 2023-10-07 21:25:28 +0800
lang: en
categories: games maimai
---

## 0. Introduction

Tired of going to the laundry house every day? You can play with the washing machines at home. However, finding appropriate resources can be quite a tough process. This is an early, immature guide for you to build your own database to play on any platforms supported by AstroDX.

**Disclaimer:** In this tutorial, the author assume that you are computer-literate. Readers *should* verify the validity and safety of everything described here before running them on their device. Readers are expected to have these abilities: 1. Working with [.NET](https://dotnet.microsoft.com/) toolchains; 2. Running [Node.js](https://nodejs.org/) scripts; 3. Use [PowerShell Core](https://learn.microsoft.com/en-us/powershell/); 4. Basic knowledge in reverse engineering of [Unity](https://unity.com/) programs. The author is not affiliated with any of the parties mentioned in this guide, and is not responsible for any actions readers have made. *You are on your own now. Proceed with caution.*

**Software needed:**

* AstroDX (<https://github.com/2394425147/maipaddx>): Game simulator
* MaichartConverter (<https://github.com/Neskol/MaichartConverter>): Chart converter
* CriTools (<https://github.com/kohos/CriTools>): Music converter
* WannaCRI (<https://github.com/donmai-me/WannaCRI>): Video converter
* FFmpeg (<https://ffmpeg.org/>): Various miscellaneous conversions
* AssetStudio (<https://github.com/Perfare/AssetStudio>): Finding magic keys
* script-collection (<https://github.com/CSharperMantle/script-collection>): One of these script will be used

**Resources may be helpful:**

* <https://www.94joy.cn/maimai/267>: (Chinese) Various resources
* <https://estertion.win/2019/10/%e6%9c%89%e5%85%b3%e4%ba%8ecriware%e7%9a%84%e4%b8%80%e7%82%b9%e6%9c%80%e7%bb%88%e8%a7%a3%e5%86%b3%e6%96%b9%e6%a1%88/>: (Chinese) Finding magic keys
* <https://github.com/beerpiss/astrodx-guide>: Guide for importing built database into AstroDX

## 1. Getting initial resources.

This part is quite straightforward if you know where to find. The process of searching for related resources is not described here.

**Expected artifacts:**

* `^.+\.vhd$`: Hard disk image in `vhd` format.

## 2. Create chart files

Mount `vhd` file you have obtained above. We assume that you mount it as `X:` hereafter.

Download and build MaichartConverter. Run this command to convert `.ma2` files to `^(.+)\\maidata.txt$` Simai charts, where the first capture here is the score name:

```powershell
PS > MaichartConverter.exe CompileDatabase -p="X:\Package\Sinmai_Data\StreamingAssets\A000\" -o "<OUTDIR>" -f="simai" -g=6
```

See the help of MaichartConverter for more info about these parameters. Basically, it will generate a bunch of folders under `<OUTDIR>`, each of these folders is named after a score and contains a `maidata.txt` score file. Copy all of these into a folder named `chart`.

**Expected artifacts:**

* `<OUTDIR>\\chart\\[1-9][0-9]*_.+\\\maidata.txt$`: Generated charts.

## 3. Obtain magic key

Refer to <https://estertion.win/2019/10/%e6%9c%89%e5%85%b3%e4%ba%8ecriware%e7%9a%84%e4%b8%80%e7%82%b9%e6%9c%80%e7%bb%88%e8%a7%a3%e5%86%b3%e6%96%b9%e6%a1%88/> for more information on this topic. We will not cover it here.

Once you have obtained the magic key (which is a `uint64_t` decimal), convert it into Hex format (like `0xdeadbeef11223344`). We denote this as `<KEY>` hereafter.

**Expected artifacts:**

* `<KEY>`: Magic key in hex format.

## 4. Extract music and video

Run this script:

```powershell
$MusicPath = "X:/Package/Sinmai_Data/StreamingAssets/A000/music"
$SoundPath = "X:/Package/Sinmai_Data/StreamingAssets/A000/SoundData"
$MoviePath = "X:/Package/Sinmai_Data/StreamingAssets/A000/MovieData"
$ChartPath = "<OUTDIR>/chart"
$OutputPath = "<OUTDIR>/maiout"
$EncKey = "<KEY>"

Set-Location -Path $OutputPath

$tmp_dir = $OutputPath + "/tmp"
if (Test-Path $tmp_dir) {
    Remove-Item "$tmp_dir/*" -Recurse
}
else {
    New-Item -Path $OutputPath -Name "tmp" -ItemType Directory
}

foreach ($d in Get-ChildItem -Path $MusicPath -Directory -Filter "music*") {
    Set-Location -Path $tmp_dir

    $music_name = $d.BaseName
    $garbage = $music_name -match "^music([0-9]{6})$"
    $music_id = $Matches.1
    $music_id_int = [int]$music_id
    if ($music_id_int -ge 10000) {
        # maimai DX files
        $garbage = $music_id -match "^01([0-9]{4})$"
        $music_id = "00$($Matches.1)"
    }
    
    $sound_path = "$SoundPath/music$music_id.acb"

    if (-not (Test-Path $sound_path -PathType Leaf)) {
        Write-Error "Sound file not found: $sound_path"
        break
    }

    $metadata_path = "$($d.FullName)/Music.xml"
    if (-not (Test-Path $metadata_path -PathType Leaf)) {
        Write-Warning "Metadata not found: $metadata_path; ignoring"
        continue
    }

    node ~/CriTools-master/src/index.js acb2wavs -k $EncKey -o $tmp_dir $sound_path
    ffmpeg -i "$tmp_dir/stream_1.wav" -codec:a libmp3lame -qscale:a 2 "$tmp_dir/track.mp3"
    Remove-Item "$tmp_dir/stream_1.wav"

    foreach ($c in Get-ChildItem -Path $ChartPath -Directory) {
        if ($c.BaseName -match "^$($music_id_int)_.+$") {
            $chart_folder_path = $c.FullName
            break
        }
    }
    $chart_path = "$chart_folder_path/maidata.txt"
    Copy-Item -Path $chart_path -Destination "$tmp_dir/maidata.txt"

    wannacri extractusm "$MoviePath/$music_id.dat" -k $EncKey

    $movie_export_path = "$tmp_dir/output/$music_id.dat/videos"
    if (-not (Test-Path $movie_export_path -PathType Container)) {
        Write-Warning "Exported movie not found: $movie_export_path; ignoring"
        continue
    }
    $movie_file = Get-ChildItem -Path $tmp_dir -Filter "*.ivf" -Recurse
    $movie_file = $movie_file.FullName
    ffmpeg -i $movie_file -crf 28 -preset slow "$tmp_dir/pv.mp4"
    foreach ($r in Get-ChildItem -Path $tmp_dir -Directory) {
        Remove-Item $r.FullName -Recurse
    }

    Set-Location -Path $OutputPath
    Copy-Item -Path $tmp_dir -Destination "$OutputPath/$music_name" -Recurse
    Remove-Item "$tmp_dir/*" -Recurse
}

Remove-Item $tmp_dir -Recurse
```

You will find that various folders are created under `<OUTDIR>\\maiout\\` with the names like `^music[0-9]{6}$`.

**Expected artifacts:**

* `^<OUTDIR>\\maiout\\music[0-9]{6}\\$`: Generated song packs.

## 5. Sort and import

Run `Sort-Maidata-Scores-By-Genre.ps1` from my [script-collection](https://github.com/CSharperMantle/script-collection):

```powershell
PS > ./Sort-Maidata-Scores-By-Genre.ps1 -Path <OUTDIR>
```

You can see all these charts are categorized into folders. Now copy all these files to your platform according to instructions given by <https://github.com/beerpiss/astrodx-guide>.

Congratulations! You have a working database now. Try to play with it at home without hassles!
