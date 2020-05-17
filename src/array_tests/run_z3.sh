for f in horn*.smt2; do
echo $f
timeout 60 time z3 $f 
done