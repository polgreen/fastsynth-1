for f in *.sl; do
echo $f
timeout 60 time fastsynth --arrays $f 
done