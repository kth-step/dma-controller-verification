/home/jhagl/PhD/sources/HOL/bin/Holmake -r clean;
find -type d -name ".hollogs" -prune -exec rm -rf {} \;
find -type d -name ".HOLMK" -prune -exec rm -rf {} \;
find . -name "*~" -type f -delete;
find . -name "*Theory.sig" -type f -delete;
find . -name "*Theory.sml" -type f -delete;
find . -name "*Theory.dat" -type f -delete;
find . -name "*Theory.ui" -type f -delete;
find . -name "*Theory.uo" -type f -delete;
find . -name "*Script.ui" -type f -delete;
find . -name "*Script.uo" -type f -delete;

find . -name "helper_tactics.ui" -type f -delete;
find . -name "helper_tactics.uo" -type f -delete;
find . -name "ltac.ui" -type f -delete;
find . -name "ltac.uo" -type f -delete;
