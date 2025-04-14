---
layout: post
title: "Building chart database for AstroDX: Revisited"
date: 2023-04-13T08:19:48+08:00
lang: en
tags: topic:misc game maimai-dx astrodx
---

**See [the previous article]({% link _posts/2023-10-07-astrodx-database-construction.md %}) for a list of needed tools and supplementary tutorials.**

------

The first step is, as always, obtaining a copy of original game image. If you have an ".app" file, refer to [this awesome post](https://nyac.at/posts/from-app-to-playable-game) to decrypt it into a mountable VHD. An extra note: When you are asked to use [ImDisk](https://sourceforge.net/projects/imdisk-toolkit/) ([Chocolatey](https://community.chocolatey.org/packages/ImDisk-Toolkit)), *just use it.* Don't use any "remastered" versions. They lack critical features.

These revised scripts utilize [MaichartConverter](https://github.com/Neskol/MaichartConverter)'s built-in database creation feature. That tool has some peculiarities of its own:

* For a chart with ID 123456, its corresponding BGA file should be "003456.mp4", and its sound file should be "music003456.mp3"
* All chart variants (DX/Party charts) corresponds to the same BGA and sound files. For example, chart 00abcd, 01abcd, 10abcd, 11abcd, 12abcd, ... all corresponds to "00abcd.mp4", "music00abcd.mp3", etc.

## Scripts

### Prepare-Maichart-Sound.ps1

```powershell
param (
    [boolean]$Overwrite = $false,
    [string]$MusicPath,
    [string]$SoundPath,
    [string]$OutputPath,
    [string]$CriToolsPath,
    [string]$EncKey,
    [uint32]$Parallelism = 24
)


Get-ChildItem -Path $MusicPath -Directory -Filter "music*" | Foreach-Object -ThrottleLimit $Parallelism -Parallel {
    function New-TemporaryDirectory {
        $tmp = [System.IO.Path]::GetTempPath() # Not $env:TEMP, see https://stackoverflow.com/a/946017
        $name = (New-Guid).ToString("N")
        New-Item -ItemType Directory -Path (Join-Path $tmp $name)
    }

    $music_name = $PSItem.BaseName
    if (-not ($music_name -match "^music([0-9]{6})$")) {
        Write-Warning "Invalid music name: $music_name"
        break
    }
    $music_id = $Matches.1
    $music_id_int = [int]$music_id
    if ($music_id_int -ge 10000) {
        if (-not ($music_id -match "^[0-9]{2}([0-9]{4})$")) {
            Write-Warning "Invalid DX/Party music name: $music_name"
            break
        }
        $music_id = "00$($Matches.1)"
    }
  
    $sound_path = "$USING:SoundPath/music$music_id.acb"

    if (-not (Test-Path $sound_path -PathType Leaf)) {
        Write-Warning "Sound file not found: $sound_path"
        break
    }

    $metadata_path = "$($PSItem.FullName)/Music.xml"
    if (-not (Test-Path $metadata_path -PathType Leaf)) {
        Write-Warning "Metadata not found: $metadata_path"
        break
    }

    if (-not $USING:Overwrite -and (Test-Path "$USING:OutputPath/music$music_id.mp3" -PathType Leaf)) {
        Write-Warning "Skipping existing music$music_id.mp3"
        break
    }
    
    $tmp_dir = New-TemporaryDirectory

    node.exe $USING:CriToolsPath/src/index.js acb2wavs -k $USING:EncKey -o $tmp_dir $sound_path
    ffmpeg.exe -hide_banner -loglevel error -i "$tmp_dir/stream_1.wav" -codec:a libmp3lame -qscale:a 2 "$tmp_dir/stream_1.mp3"
    Remove-Item "$tmp_dir/stream_1.wav"
    Move-Item -Path "$tmp_dir/stream_1.mp3" -Destination "$USING:OutputPath/music$music_id.mp3" -Force

    Remove-Item -Path $tmp_dir -Recurse
}
```

Run this script as follows:

```powershell
.\Prepare-Maichart-Sound.ps1 -MusicPath "X:/Package/Sinmai_Data/StreamingAssets/A000/music" -SoundPath "X:/Package/Sinmai_Data/StreamingAssets/A000/SoundData" -OutputPath "[Your output path]/sound_out" -CriToolsPath "[Cloned CriTools root]" -EncKey "0x[Your encryption key in HEX]"
```

### Prepare-Maichart-Movie.ps1

```powershell
param (
    [boolean]$Overwrite = $false,
    [string]$MusicPath,
    [string]$MoviePath,
    [string]$OutputPath,
    [string]$EncKey,
    [uint32]$Parallelism = 2
)


Get-ChildItem -Path $MusicPath -Directory -Filter "music*" | Foreach-Object -ThrottleLimit $Parallelism -Parallel {
    function New-TemporaryDirectory {
        $tmp = [System.IO.Path]::GetTempPath() # Not $env:TEMP, see https://stackoverflow.com/a/946017
        $name = (New-Guid).ToString("N")
        New-Item -ItemType Directory -Path (Join-Path $tmp $name)
    }

    $music_name = $PSItem.BaseName
    if (-not ($music_name -match "^music([0-9]{6})$")) {
        Write-Warning "Invalid music name: $music_name"
        break
    }
    $music_id = $Matches.1
    $music_id_int = [int]$music_id
    if ($music_id_int -ge 10000) {
        if (-not ($music_id -match "^[0-9]{2}([0-9]{4})$")) {
            Write-Warning "Invalid DX/Party music name: $music_name"
            break
        }
        $music_id = "00$($Matches.1)"
    }

    $metadata_path = "$($PSItem.FullName)/Music.xml"
    if (-not (Test-Path $metadata_path -PathType Leaf)) {
        Write-Warning "Metadata not found: $metadata_path"
        break
    }

    if (-not $USING:Overwrite -and (Test-Path "$USING:OutputPath/$music_id.mp4" -PathType Leaf)) {
        Write-Warning "Skipping existing $music_id.mp4"
        break
    }
    
    $tmp_dir = New-TemporaryDirectory

    wannacri.exe extractusm -k $USING:EncKey -o $tmp_dir "$USING:MoviePath/$music_id.dat"

    $movie_export_path = "$tmp_dir/$music_id.dat/videos"
    if (-not (Test-Path $movie_export_path -PathType Container)) {
        Write-Warning "Exported movie not found: $movie_export_path; ignoring"
        continue
    }
    $movie_file = Get-ChildItem -Path $tmp_dir -Filter "*.ivf" -Recurse
    $movie_file = $movie_file.FullName
    ffmpeg.exe -hide_banner -loglevel error -stats -hwaccel cuda -i $movie_file -c:v hevc_nvenc -rc:v vbr -cq:v 32 -qmin 30 -qmax 36 -an "$tmp_dir/$music_name.mp4"
    Move-Item -Path "$tmp_dir/$music_name.mp4" -Destination "$USING:OutputPath/$music_id.mp4" -Force

    Remove-Item -Path $tmp_dir -Recurse
}
```

Run this script as follows:

```powershell
.\Prepare-Maichart-Movie.ps1 -MusicPath "X:/Package/Sinmai_Data/StreamingAssets/A000/music" -MoviePath "X:/Package/Sinmai_Data/StreamingAssets/A000/MovieData" -OutputPath "[Your output path]/movie_out" -EncKey "0x[Your encryption key in HEX]"
```
