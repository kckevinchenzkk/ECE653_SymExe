def matmul(a, b):
    n, p = len(a), len(a[0])
    q, p1 = len(b), len(b[0])
    if p!= p1:
        raise ValueError("Imcompatiable dime")
    c =[[0] * q for i in range(n)]
    for i in range(n):
        for j in range(q):
            c[i][j] = sum(a[i][k] * b[k][j] for k in range(p))
    return c
  
if __name__ == "__main__":
    a = None
    b = None
    a = [[5,7], [8,21]]
    b = [[8], [4]]
    print(matmul(a,b))





class RepeatUntilStmt(Stmt):
    def __init__(self, cond, body, inv=None):
        self.cond = cond
        self.body = body
        self.inv = inv



    

