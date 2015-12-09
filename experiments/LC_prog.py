import operator as op
import inspect

Var = 'var'
Lam = 'lam'
App = 'app'

Clo = 'clo'
Prim = 'prim'
Int = 'int'
Fun = 'fun'
Bool = 'bool'
List = 'list'
Str = 'str'
Unit = 'unit'


def app(f, *vs):
    try:
        f[0]
        if isinstance(f, str):
            f = [Var, f]
        ans, *vs = vs
        ans = [App, f, ans]
        for v in vs:
            if isinstance(v, str):
                v = [Var, v]
            ans = [App, ans, v]
        return ans
    except ValueError as e:
        raise e


def lam(xs, b):
    if isinstance(b, str):
        b = [Var, b]
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


def clo(lam, env=None):
    if not env:
        env = []
    _lam, body = to_de_bruijn(lam)
    return [Clo, body, env]


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


def s(s):
    return [Prim, Str, s]


bottom = None

'''
Y = λf. (λx. (f (x x))) (λx. (f (x x)))
'''
Y = lam('f', app(lam('x', app('f', app('x', 'x'))),
                 lam('x', app('f', app('x', 'x')))))
bottom = app(Y, Y)

iden = lam('x', 'x')

unit = [Prim, Unit]


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
             app('if',
                 app('==', 'n', [Prim, Int, 0]),
                 'nil',
                 app('xs',
                     lam(['x', 'xs'],
                         app('cons',
                             'x',
                             app('take', app('-1', 'n'), 'xs'))),
                     'nil'))))

'''
(!!) (x:xs) 0 = x
(!!) (_:xs) n = (!!) xs (n-1)
(!!) [] 0 = bottom
'''
idx = y(lam(['!!', 'xs', 'n'],
            app('if', app('==', 'n', '0'),
                app('xs', 'fst', 'bottom'),
                app('xs',
                    lam(['_', 'xs'], app('!!', 'xs', app('-1', 'n'))),
                    'bottom'))))

'''
head xs = xs (\ x xs -> x) bottom
'''
head = lam('xs', app('xs', lam(['x', 'xs'], 'x'), 'bottom'))

'''
tail xs = xs (\ x xs -> xs) bottom
'''
tail = lam('xs', app('xs', lam(['x', 'xs'], 'xs'), 'bottom'))

'''
zipWith = \ f -> Y $ zip a b ->
    a (\ x xs -> b (\ y ys -> cons (f x y) (zip xs ys)) nil ) nil
'''
zipWith = lam('f',
              y(lam(['zipWith_', 'a', 'b'],
                    app('a',
                        lam(['x', 'xs'],
                            app('b',
                                lam(['y', 'ys'],
                                    app('cons',
                                        app('f', 'x', 'y'),
                                        app('zipWith_', 'xs', 'ys'))),
                                'nil')),
                        'nil'))))

'''
fibs = 1 : 1 : zipWith (+) fibs (tail fibs)
'''
fibs = y(lam('fibs',
             app('cons',
                 '1',
                 app('cons',
                     '1',
                     app('zipWith', '+', 'fibs', app('tail', 'fibs'))))))

'''
type State s a = s -> (a, s)
(>>=) :: State a -> (a -> State b) -> State b
(>>=) :: (s -> (a, s)) -> (a -> s -> (b, s)) -> s -> (b, s)
(>>=) s f = λx -> let (a, s') = s x in f a s'
stateBind = λs f x. s x (λa s'. f a s')
stateReturn = λx s. pair x s
'''
state_bind = lam(['s', 'f', 'x'],
                 app('s', 'x', lam(['a', "s'"], app('f', 'a', "s'"))))
state_return = lam('x', lam('s', app('pair', 'x', 's')))


def fun(f):
    args, varargs, varkw, defaults = inspect.getargspec(f)
    return [Prim, Fun, f, len(args), []]


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


def pred_int(expr):
    _prim, _int, x = expr
    return [_prim, Int, x-1]


def op_int(op):
    def f(a, b):
        _prim, _int, m = a
        _prim, _int, n = b
        return [_prim, _int, op(m, n)]
    return f


def from_bool(expr):
    _prim, _bool, x = expr
    return true if x else false

if_ = lam(['p', 't', 'f'], app(fun(from_bool), 'p', 't', 'f'))


def eq_prim(expr_a, expr_b):
    _prim, t1, x = expr_a
    _prim, t2, y = expr_b
    return [Prim, Bool, t1 == t2 and x == y]


'''
class show a where
    show :: a -> String
'''


def show_int(n):
    _prim, _int, x = n
    return [Prim, Str, repr(x)]


def show_list(show_a):
    def show_list_with_show_a(xs):
        _prim, _list, xs = xs
        return [Prim,
                Str,
                '[{}]'.format(', '.join(map(lambda x: show_a(x)[2], xs)))]
    return show_list_with_show_a


# 這裡應該要 curry 嗎？
def show_tuple(show_a, show_b):
    def show_tuple(a):
        def show_tuple_a(b):
            _prim, _str, a_ = show_a(a)
            _prim, _str, b_ = show_b(b)
            return [Prim, Str, '({}, {})'.format(a_, b_)]
        return fun(show_tuple_a)
    return clo(lam('tuple', app('tuple', fun(show_tuple))))


def putStrLn_prim(x):
    _prim, _str, s = x
    print(s)
    return clo(lam('s', app(pair, unit, 's')))


def putChar_prim(x):
    _prim, _str, s = x
    print(s[0], end='')
    return lam('s', app(pair, unit, 's'))


def is_string_prim(x):
    ans = x[0] == Prim and x[1] == Str
    return [Prim, Bool, ans]

putStrLn = y(lam(['putStrLn', 'cs'],
                 app('if', app(fun(is_string_prim), 'cs'),
                     app(fun(putStrLn_prim), 'cs'),
                     app('cs',
                         lam(['c', 'cs'],
                             app('ioBind',
                                 app('putChar', 'c'),
                                 lam('_', app('putStrLn', 'cs')))),
                         app('putChar', s('\n'))))))


def getLineWithPrompt_prim(x):
    _prim, _str, prompt = x
    r = input(prompt)
    return lam('s', app(pair, [Prim, Str, r], 's'))


def getLine_prim(s):
    r = input()
    return lam('p', app('p', [Prim, Str, r], s))


def cons_prim(x, xs):
    _prim, _list, xs = xs
    return [_prim, _list, [x]+xs]


def do(monad, *stmts):
    '''
    do (monad) { name = expr ; ...rest }
        = expr >>= λname. do (monad) { rest }
    do (monad) { expr ; ... rest }
        = expr >>= λ_. do (monad) { rest }
    do (monad) { expr }
        = expr
    '''
    def _do(stmts):
        stmt, *stmts = stmts
        name = '_'
        if isinstance(stmt, tuple):
            name, stmt = stmt
        if stmts:
            return app('##bind', stmt, lam(name, _do(stmts)))
        else:
            return stmt
    return app(monad, lam(['##bind', 'return'], _do(list(stmts))))


def prelude(prog):
    fs = [('Y', Y),
          ('bottom', bottom),
          ('()', unit),
          ('True', [Prim, Bool, True]),
          ('False', [Prim, Bool, False]),
          ('const', const),
          ('fst', true),
          ('snd', false),
          ('+1', fun(succ_int)),
          ('-1', fun(pred_int)),
          ('+', fun(op_int(op.add))),
          ('-', fun(op_int(op.sub))),
          ('*', fun(op_int(op.mul))),
          ('div', fun(op_int(op.floordiv))),
          ('mod', fun(op_int(op.mod))),
          ('if', if_),
          ('""', [Prim, Str, ""]),
          ('==', fun(eq_prim)),
          ('succ', succ),
          ('add', add),
          ('cons', cons),
          ('nil', nil),
          ('head', head),
          ('tail', tail),
          ('pair', pair),
          ('take', take),
          ('zipWith', zipWith),
          ('ioBind', state_bind),
          ('ioReturn', state_return),
          ('state_monad', app('pair', state_bind, state_return)),
          ('putChar', fun(putChar_prim)),
          ('putStrLn', putStrLn),
          ('getLineWithPrompt', fun(getLineWithPrompt_prim)),
          ('getLine', fun(getLine_prim)),
          ('runIO', lam('m', app('m', '()', lam(['_', '_'], '()'))))
          ]
    return define(fs)(prog)
