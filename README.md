# BrightBounceVRAD-OrangeBox
Light bouncing from Goldsource ported to Source (to avoid original HL2's impression of Doom2 per-sector lighting)

Produces brighter indirect lighting (bounced lighting) than stock OrangeBox VRAD. ZHLT tier bouncing is now fully implemented.

How to enable the algo:  
-ZHLTbounce -uniform (effect boost, can be used separately)

Hardcoded cloud lighting for skyboxes, that are used on maps before Ravenholm:  
-Cloudlight

Autobalance algo to figure out the optimal number of bounces.
(prevents the bouncing light from a chain reaction)
Active by default unless a bounce number was specified. Typically gives you 3-4 bounces. Stops if next bounce was weakened by less than 10%.

Since HL2 was made with so much fake lighting, clean it up:  
-LightingFixes

How I compiled the maps:
"D:\Ultimate SSDK v3\SourceSDK\Bin\source2009\bin\vrad.exe" -low -threads 9 -StaticPropPolys -StaticPropLighting -TextureShadows -Final -LightingFixes -ZHLTbounce -Uniform -Cloudlight -LargeDispSampleRadius "D:\games\Half-Life_2_Update\hl2\maps\background01"

For debug purposes you can disable different lighting types or all at once:  
-SkipPointlights  
-SkipSpotlights  
-SkipSunSky

Misc:  
-ForceTexlights
-DebugClouds

Default game (HL2: Update):
![e7e8a8452e8e8d6d8c939730673c25ff](https://github.com/user-attachments/assets/70a17d48-a8ed-4424-985c-14025398402b)

-ZHLTbounce
![7fe6926858812574160a6d8e79365c7b](https://github.com/user-attachments/assets/184fdba3-6d4f-4527-aa9b-31c6ba50562f)

-ZHLTbounce -uniform
![fac51803c3a0ce9577a9ace96b1c0383](https://github.com/user-attachments/assets/25c5c0a4-de9e-4f5f-9baa-cf63a7004f00)


