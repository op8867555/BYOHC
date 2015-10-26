Var = 'var'
Lam = 'lam'
App = 'app'

Clo = 'clo'
Prim = 'prim'
Int = 'int'
Fun = 'fun'
Bool = 'bool'
List = 'list'


def app(f, *vs):
    try:
        f[0]
        ans, *vs = vs
        ans = [App, f, ans]
        for v in vs:
            ans = [App, ans, v]
        return ans
    except ValueError as e:
        raise e


def lam(xs, b):
    if not isinstance(xs, list):
        return [Lam, xs, b]
    ans, *xs = reversed(xs)
    ans = [Lam, ans, b]
    for x in xs:
        ans = [Lam, x, ans]
    return ans


def var(x):
    return [Var, x]


def to_de_bruijn(expr, stack=None):
    if not stack:
        stack = []
    if isinstance(expr, str):
        expr = [Var, expr]
    try:
        typ, x = expr[0:2]
    except ValueError:
        raise Exception('to_de_bruijn: ' + repr(expr))
    if typ == Lam:
        body = expr[2]
        return [Lam, to_de_bruijn(body, [x] + stack)]
    elif typ == Var:
        idx = stack.index(x)
        return [Var, idx]
    elif typ == App:
        y = expr[2]
        return [App, to_de_bruijn(x, stack), to_de_bruijn(y, stack)]
    else:
        return expr


def scott_to_int(x):
    z = to_de_bruijn(c0)
    if x == z:
        return 0
    else:
        [_l, [_l, [_app, _s, n]]] = x
        return scott_to_int(n) + 1


def scott_to_list(xs, f=None):
    n = to_de_bruijn(nil)
    if xs == n:
        return []
    else:
        [_l, [_l, [_a, [_a, _c, x], xs]]] = xs
        if f:
            x = f(x)
        return [x] + scott_to_list(xs, f)


def nat(x):
    n = lam(['s', 'n'], [Var, 'n'])
    for i in range(x):
        n = lam(['s', 'n'], app('s', n))
    return n


bottom = None

'''
Y = λf. (λx. (f (x x))) (λx. (f (x x)))
'''
Y = lam('f', app(lam('x', app('f', app('x', 'x'))),
                 lam('x', app('f', app('x', 'x')))))
bottom = app(Y, Y)


def y(expr):
    return app('Y', expr)


c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 = map(nat, range(10))

true = lam(['t', 'f'], 't')
false = lam(['t', 'f'], 'f')

const = true
succ = lam(['n', 's', 'z'], app('s', 'n'))
pred = lam('n', app('n', lam('n-', 'n-'), c0))


add = y(lam(['+', 'a', 'b'],
            app('a', lam('a-', app('+', 'a-', app('succ', 'b'))), 'b')))

'''
const a b = a
eq m n = m (\m-. n (\n-. eq m- n-)) false) (n (const false) true)
'''
eq = y(lam(['eq_', 'm', 'n'],
       app('m',
           lam('m-',
               app('n', lam('n-', app('eq_', 'm-', 'n-')), 'false')),
           app('n', app('const', 'false')), 'true')))

cons = lam(['h', 't', 'cons', 'nil'], app('cons', 'h', 't'))

nil = lam(['cons', 'nil'], 'nil')

pair = lam(['a', 'b', 'p'], app('p', 'a', 'b'))

'''
take n xs = n (\ n- -> xs (\ x xs -> (:) x (take n- xs)) nil) nil

take _ [] = []
take 0 _ = []
take n (x:xs) = x : take (n-1) xs
'''
take = y(lam(['take', 'n', 'xs'],
             app('n',
                 lam('n-',
                     app('xs',
                         lam(['x', 'xs'],
                             app('cons', 'x', app('take', 'n-', 'xs'))),
                         'nil')),
                 'nil')))

'''
tail xs = xs (\ x xs -> xs) bottom
'''
tail = lam('xs', app(lam(['x', 'xs'], 'xs'), 'bottom'))

'''
zipWith = Y $ \ zip_ f a b ->
    a (\ x xs -> b (\ y ys -> cons (f x y) (zip_ xs ys)) nil ) nil
'''
zipWith = y(lam(['zipWith_', 'f', 'a', 'b'],
                app('a',
                    lam(['x', 'xs'],
                        app('b',
                            lam(['y', 'ys'],
                                app('cons',
                                    app('f', 'x', 'y'),
                                    app('zipWith_', 'xs', 'ys'))),
                            'nil')),
                    'nil')))

'''
fibs = 1 : 1 : zipWith (+) fibs (tail fibs)
'''
fibs = y(lam('fibs',
             app('cons',
                 '1',
                 app('cons',
                     '1',
                     app('zipWith', '+', 'fibs', app('tail', 'fibs'))))))


def fun(expr):
    return [Prim, Fun, expr]


def scott_list(xs, f=None):
    ys = nil
    for x in reversed(xs):
        if f:
            x = f(x)
        ys = app(app(cons, x), ys)
    return ys


def define(xs):
    def ret(x):
        res = x
        for (name, fun) in reversed(xs):
            res = app(lam(name, res), fun)
        return res
    return ret


def succ_int(expr):
    _prim, _int, x = expr
    return [_prim, Int, x+1]


def add_int(a):
    def add_a(b):
        _prim, _int, m = a
        _prim, _int, n = b
        return [_prim, _int, m + n]
    return [Prim, Fun, add_a]


def if_prim(expr):
    def if1(a):
        def if2(b):
            _prim, _bool, x = expr
            return a if x else b
        return fun(if2)
    return fun(if1)


'''
to_int = λx x ( λx- succ(to_int x-)) 0
'''
to_int = y(lam(['to_int', 'x'],
               app('x',
                   lam('x-', app('+1',
                                 app('to_int', 'x-'))),
                   '0')))


to_list = y(lam(['to_list_', 'xs'],
                app('xs',
                    lam(['x', 'xs'],
                        app(':', 'x', app('to_list_', 'xs'))),
                    '[]')))


def print_prim(x):
    print(x)
    return x


def cons_prim(x):
    def cons_x(xs):
        _prim, _list, xs = xs
        return [_prim, _list, [x]+xs]
    return [Prim, Fun, cons_x]


def prelude(prog):
    fs = [('Y', Y),
          ('bottom', bottom),
          ('0', [Prim, Int, 0]),
          ('1', [Prim, Int, 1]),
          ('+1', [Prim, Fun, succ_int]),
          ('+', [Prim, Fun, add_int]),
          ('if', [Prim, Fun, if_prim]),
          ('to_int', to_int),
          ('print', [Prim, Fun, print_prim]),
          ('[]', [Prim, List, []]),
          (':', [Prim, Fun, cons_prim]),
          ('succ', succ),
          ('to_list', to_list),
          ('cons', cons),
          ('nil', nil),
          ('tail', tail),
          ('take', take),
          ('zipWith', zipWith)
          ]
    return define(fs)(prog)
