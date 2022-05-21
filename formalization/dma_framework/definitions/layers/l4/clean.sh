/home/jhagl/PhD/sources/HOL/bin/Holmake -r clean;
find -type d -name ".hollogs" -prune -exec rm -rf {} \;
find -type d -name ".HOLMK" -prune -exec rm -rf {} \;
find . -name "*~" -type f -delete;
