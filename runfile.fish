function runfile -a pathname
  cabal run $pathname
  and ld $pathname".o" -lc -arch x86_64 -o a.out
  and rm $pathname".o"
  and ./a.out
  echo "status:" $status
end