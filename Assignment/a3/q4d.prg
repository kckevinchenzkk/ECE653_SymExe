havoc x, y; assume y >= 0; assume x >= 0; j:= y; r:=x; while r < y inv (r = y - j) and (x >= 0) do{r := r + 1; j := j - 1}; assert r = y"
