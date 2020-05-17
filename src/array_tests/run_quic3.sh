for f in quic3*.smt2; do
echo $f
timeout 60 time z3 $f 
done