---
layout: default
---
# Overview

## Recent projects

### Project **Invaders**
[Original source](https://github.com/CSharperMantle/Invaders/)
![Snapshot](invaders_snapshot.png)

#### Core algorithms

##### History data recorder

```csharp
private void ReadHistoryDataFromFile()
{
    if (!Directory.Exists(HistoryDataDirectory)) Directory.CreateDirectory(HistoryDataDirectory);
    if (!File.Exists(HistoryDataFilePath))
    {
        _historyData = new HistoryData();
        return;
    }

    using (Stream reader = File.OpenRead(HistoryDataFilePath))
    {
        try
        {
            var serializer = new DataContractJsonSerializer(typeof(HistoryData));
            var obj = serializer.ReadObject(reader);
            if (obj is HistoryData)
                _historyData = obj as HistoryData;
            else
                throw new SerializationException(nameof(obj) + " is not " + nameof(HistoryData));
        }
        catch (Exception e)
        {
            Log.Critical(e.ToString());
            Log.Info(e.StackTrace);
            _historyData = new HistoryData();
        }
       
    }
}

private void WriteHistoryDataFromFile()
{
    if (_historyData == null) throw new SerializationException(nameof(_historyData) + " is null.");
    try
    {
        if (!File.Exists(HistoryDataFilePath))
            using (Stream creater = File.Create(HistoryDataFilePath))
            {
                var serializer = new DataContractJsonSerializer(typeof(HistoryData));
                serializer.WriteObject(creater, _historyData);
            }
            else
            using (Stream writer = File.OpenWrite(HistoryDataFilePath))
            {
                var serializer = new DataContractJsonSerializer(typeof(HistoryData));
                serializer.WriteObject(writer, _historyData);
            }
    }
    catch (Exception e)
    {
        Log.Critical(e.ToString());
        Log.Info(e.StackTrace);
    }
            
}
```

##### Console logger

```csharp
using System;

namespace Invaders.Wpf.Commons
{
    public static class Log
    {
        public static void Info(string message)
        {
            var beforeColor = Console.ForegroundColor;
            Console.ForegroundColor = ConsoleColor.White;
            Console.WriteLine("[Info]>>{0}", message);
            Console.ForegroundColor = beforeColor;
        }

        public static void Debug(string message)
        {
            var beforeColor = Console.ForegroundColor;
            Console.ForegroundColor = ConsoleColor.Blue;
            Console.WriteLine("[DEBUG]>>{0}", message);
            Console.ForegroundColor = beforeColor;
        }

        public static void Warning(string message)
        {
            var beforeColor = Console.ForegroundColor;
            Console.ForegroundColor = ConsoleColor.Yellow;
            Console.WriteLine("[WARNING]>>{0}", message);
            Console.ForegroundColor = beforeColor;
        }

        public static void Strict(string message)
        {
            var foregroundColor = Console.ForegroundColor;
            var backgroundColor = Console.BackgroundColor;
            Console.ForegroundColor = ConsoleColor.Yellow;
            Console.BackgroundColor = ConsoleColor.Blue;
            Console.WriteLine("[STRICT]>>{0}", message);
            Console.ForegroundColor = foregroundColor;
            Console.BackgroundColor = backgroundColor;
        }

        public static void Error(string message)
        {
            var foregroundColor = Console.ForegroundColor;
            var backgroundColor = Console.BackgroundColor;
            Console.ForegroundColor = ConsoleColor.Yellow;
            Console.BackgroundColor = ConsoleColor.Red;
            Console.Error.WriteLine("[ERROR]>>{0}", message);
            Console.ForegroundColor = foregroundColor;
            Console.BackgroundColor = backgroundColor;
        }

        public static void Critical(string message)
        {
            var foregroundColor = Console.ForegroundColor;
            Console.BackgroundColor = ConsoleColor.Red;
            Console.WriteLine("[CRITICAL]>>{0}", message);
            Console.ForegroundColor = foregroundColor;
        }
    }
}
```

#### Customizing and editing your history data
**Data format**
```json
{"DiedTime":0,"HighestScore":0,"KilledInvaders":0,"PlayedGames":0,"PlayedTime":"PT0S"}
```
**DiedTime**: Death times of the player. Type: int.
**HighestScore**: The highest score the player gets. Type: int
**KilledInvaders**: Invaders the player killed. Type: int
**PlayedGames**: Games the Player played. Type: int
**PlayedTime**: The time the player played. Type: System.TimeSpan?

#### Known issues
1. _Playarea_ Border doesn't have borders and corners in right way.
2. Crash when the window is too small.
3. _Scanline_ Rectangle and Canvas appears odd when the window is too small.