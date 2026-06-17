# Field Recognition Companion

Android companion app for on-site expert identity recognition. The app connects to a supported wearable capture SDK, performs local face pre-screening on the phone, crops suitable face regions, sends valid candidates to a cloud recognition service, and stores recent recognition results for review.

## Features

- On-device face pre-screening before cloud requests
- Face-region crop and upload preparation
- Cloud expert matching result display
- Recent photo recognition from the phone gallery
- Recent recognition history with retry and deletion actions
- Diagnostic logging for field testing

## Project Structure

- `app/build.gradle`: Android app configuration and dependencies
- `app/src/main/AndroidManifest.xml`: Android permissions and app entry point
- `app/src/main/java/com/bidding/glasses/MainActivity.kt`: main connection, capture, gallery recognition, local pre-screening, cloud matching, and history flow
- `app/src/main/res/layout/activity_main.xml`: main mobile UI

## Build

```powershell
.\gradlew.bat :app:assembleDebug
```

The debug APK is generated at:

```text
app/build/outputs/apk/debug/app-debug.apk
```

## Notes

This project is intended for controlled field testing with a configured cloud recognition backend. Device permissions, wearable SDK authorization, network reachability, and real-world capture quality should be verified on target hardware before production use.
