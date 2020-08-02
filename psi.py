#!/usr/bin/env python
# -*- coding: utf-8 -*-
# Buchholz ψ analyzer
# written by Fish
#
# When environmental variable SCRIPT_NAME is set, it runs as a CGI program.
# Otherwise it runs as a commandline program.
#
# Buchholz, W. (1986): A New System of Proof-Theoretic Ordinal Function.
#   Annals of Pure and Applied Logic, 32:195-207.
#   https://doi.org/10.1016/0168-0072(86)90052-7

name = 'Buchholz ψ analyzer'
version = '1.0'
url = 'https://github.com/kyodaisuu/psi'


def testOrdinal():
    """Test ordinal class
    """
    # Invalid expressions where invalidString properties are set as True
    assert ordinal(1).invalidString
    assert ordinal(1).errMessage == 'Type of parameter is not string'
    assert ordinal('a').invalidString
    assert ordinal('a').errMessage == 'Invalid character'
    assert ordinal('(#2)').invalidString
    assert ordinal('(#2)').errMessage == 'Invalid #'
    assert ordinal('0#1').errMessage == '0 is not used in array'
    assert ordinal('1#0').errMessage == '0 is not used in array'
    assert ordinal(
        '(2+1)0').errMessage == 'Number after term is invalid expression'
    assert ordinal(
        '(1)(2)').errMessage == 'Term after term is invalid expression'
    assert ordinal('2#').errMessage == 'String expected to continue'
    assert ordinal('100000').errMessage[:17] == 'Exceeding maximum'
    assert ordinal('1)').invalidString
    assert ordinal('1)').parenthesisMismatch
    assert ordinal('1)').errMessage == 'Excessive )'

    # Valid expressions
    # Parenthesis mismatch is corrected if having fewer )
    assert not ordinal('(2#1').invalidString
    assert ordinal('(2#1').parenthesisMismatch
    assert ordinal('(2#1').string == '(2#1)'  # Corrected string
    assert ordinal('(2#1').strT == '((D0(0),D0(0)),D0(0))'  # a ∈ T

    assert ordinal('0').strT == '0'
    assert ordinal('').strT == '0'
    assert ordinal('1').strT == 'D0(0)'
    assert ordinal('2').strT == '(D0(0),D0(0))'
    # # and , has same meaning
    assert ordinal('2#1').strT == '((D0(0),D0(0)),D0(0))'
    assert ordinal('(2,1)').strT == '((D0(0),D0(0)),D0(0))'
    # Space is always neglected
    assert ordinal('1 # 2 # 1').strT == '(D0(0),(D0(0),D0(0)),D0(0))'
    assert ordinal('0(1)').strT == 'D0(D0(0))'
    assert ordinal('0(1(2(0)))').strT == 'D0(D1(D2(0)))'
    # Alias for w or ω
    assert ordinal('w').strT == 'D0(D0(0))'  # w is alias for 0(0(0))
    assert ordinal('ω(0)').strT == 'Dω(0)'  # w can also be used for D_omega
    # D is always neglected. Therefore term expressions remain unchanged.
    for a in ['(D0(0),(D0(0),D0(0)))', '(D0(D1(D0(D0(0)),D0(0)),D0(D0(0))),D0(0))']:
        assert ordinal(a).strT == a

    # Principal term
    assert ordinal('0(1(2(0)))').isPT
    assert not ordinal('w#2').isPT

    # Format of results
    # Internal data structure
    assert ordinal('2#w').T == [[0, [0, []]], [[0, []], [0, []]]]
    # a ∈ T
    assert ordinal('2#w').strT == '((D0(0),D0(0)),D0(D0(0)))'
    # b ∈ OT, o(a) = o(b)
    assert ordinal('2#w').strOT == '(D0(D0(0)),(D0(0),D0(0)))'
    # Internal data structure of b
    assert ordinal('2#w').OT == [[0, [0, []]], [[0, []], [0, []]]]
    # o(a) = o(b)
    assert ordinal('2#w').ord == 'ψ0(ψ0(0))+ψ0(0)+ψ0(0)'
    # Simple expression of o(a) = o(b)
    assert ordinal('2#w').simple == 'ω+2'

    # Translation to ordinal
    assert ordinal('0(0(1(0))#1)').ord == 'ψ0(ψ1(0))'
    assert ordinal('0(2,w,1(2(1)))').ord == 'ψ0(ψ2(0))'
    assert ordinal('1,2,0(1(w(0))),10').simple == 'ψ0(ψ2(0))+13'
    assert ordinal('0(1(0(3(0))))').ord == 'ψ0(ψ1(ψ1(0)))'
    assert ordinal('1(2(0(4(0))))').isOT
    assert ordinal('2(6(3(6(0))))').isOT
    assert ordinal('0(1(4(0)),1)').ord == 'ψ0(ψ2(0))'
    assert ordinal('0(3(0),1(2(0)),1)').isOT
    assert ordinal('0(3(0),1(3(0)),1)').isOT
    assert ordinal('0(3(0),1(4(0)),1)').ord == 'ψ0(ψ3(0)+ψ2(0))'

    # Check with ordinal expressions
    for alpha in ['ψ0(ψω(ω+3)+1)', 'ψ0(ψ1(3)+ψ0(ψ0(ω)+1))']:
        assert ordinal(alpha.replace('+', '#')).simple == alpha

    return


def analyzeOrdinal(ordString):
    """Show analysis of ordinal
    """
    print('Input: ' + ordString)
    alpha = ordinal(ordString)
    if alpha.invalidString:
        print('Invalid string.')
        print(alpha.errMessage)
        return
    if alpha.parenthesisMismatch:
        print('Parenthesis corrected: ' + alpha.string)
    print('a = ' + alpha.strT)
    if alpha.isOT:
        print('where a ∈ OT.')
        print('o(a) = ' + alpha.ord)
        if alpha.ord != alpha.simple:
            print(' = ' + alpha.simple)
        return
    if len(alpha.OT) > 0:
        print('where a ∈ T, a ∉ OT. Showing b ∈ OT where o(a) = o(b):')
        print('b = ' + alpha.strOT)
        print('o(a) = o(b) = ' + alpha.ord)
        if alpha.ord != alpha.simple:
            print(' = ' + alpha.simple)
        return
    print('where a ∈ T, a ∉ OT.')
    if len(alpha.Teq) > 0:
        print('Showing b ∈ T where o(a) = o(b)')
        print('b = ' + alpha.strTeq)
    return


class ordinal(object):
    """Class of ordinal defined with Buchholz psi function

    """

    maxInt = 10000  # maximum integer to be used.
    omega = maxInt + 1

    def __init__(self, ordString):
        """Initialize

        """
        self.string = ordString
        self.parenthesisMismatch = False
        self.invalidString = False
        self.internal = False
        self.errMessage = ''
        self.T = self.strToTerm(self.string)
        if self.invalidString:
            return
        self.strT = self.TtoStr(self.T)
        self.isPT = self.termIsPT(self.T)
        self.checkOT()
        term = self.T
        isot = self.isOT
        ispt = self.isPT
        while not self.isOT:
            if len(self.Teq) > 0:
                self.T = self.Teq
                self.isPT = self.termIsPT(self.T)
                self.checkOT()
            else:
                self.isOT = False
                self.isPT = self.termIsPT(self.T)
                self.T = term
                return
        self.isOT = isot
        self.isPT = ispt
        self.OT = self.T
        self.strOT = self.TtoStr(self.OT)
        self.ord = self.OTtoOrd(self.OT)
        self.simple = self.ordToSimple(self.ord)
        self.T = term
        return

    def strToTerm(self, s):
        """Convert string to term

        """
        prevIsNum = False
        prevIsTerm = False
        adding = False
        array = []
        num = 0
        if not isinstance(s, str):
            self.invalidString = True
            self.errMessage = 'Type of parameter is not string'
            return []
        if len(s) == 0:
            return []
        if s.count('(') > s.count(')'):
            self.parenthesisMismatch = True
            s += ')' * (s.count('(') - s.count(')'))
            self.string = s
        s = s.replace(' ', '')
        s = s.replace('D', '')
        s = s.replace('ψ', '')
        s = s.replace('ω', 'w')
        if str(self.omega) in s and not self.internal:
            self.invalidString = True
            self.errMessage = 'Exceeding maximum allowed integer ' + \
                str(ordinal.maxInt)
            return
        self.internal = True
        s = s.replace('w(', str(self.omega) + '(')
        s = s.replace('w', '0(0(0))')
        i = -1
        while i < len(s)-1:  # As i may change, range cannot be used
            i += 1  # Loop i from 0 to len(s)-1
            if s[i] in '(':
                if prevIsTerm:
                    self.invalidString = True
                    self.errMessage = 'Term after term is invalid expression'
                    return []
                level = 1
                for j in range(i+1, len(s)):
                    if s[j] == '(':
                        level += 1
                    if s[j] == ')':
                        level -= 1
                    if level < 1:
                        t = self.strToTerm(s[i+1:j])
                        if prevIsNum:
                            t = [num, t]
                            prevIsNum = False
                        term = t
                        if adding:
                            array.append(t)
                        else:
                            array = [t]
                        prevIsTerm = True
                        i = j
                        break
                adding = False
                continue

            if s[i] in ')':
                self.invalidString = True
                self.parenthesisMismatch = True
                self.errMessage = 'Excessive )'
                return []

            if s[i] in '#,':
                if not prevIsTerm and not prevIsNum:
                    self.invalidString = True
                    self.errMessage = 'Invalid ' + s[i]
                    return []

                if adding:
                    if prevIsNum:
                        array.append(self.numToTerm(num))
                else:
                    if prevIsNum:
                        if num == 0:
                            self.invalidString = True
                            self.errMessage = '0 is not used in array'
                            return []
                        array = [self.numToTerm(num)]
                prevIsTerm = False
                prevIsNum = False
                num = 0
                adding = True
                continue

            if s[i] in '0123456789':
                if prevIsTerm:
                    self.invalidString = True
                    self.errMessage = 'Number after term is invalid expression'
                    return []
                if prevIsNum:
                    num = num * 10 + int(s[i])
                    if num > ordinal.omega:
                        self.invalidString = True
                        self.errMessage = 'Exceeding maximum allowed integer ' + \
                            str(ordinal.maxInt)
                        return []
                else:
                    num = int(s[i])
                    prevIsNum = True
                continue
            self.invalidString = True
            self.errMessage = 'Invalid character'
            return []
        if prevIsTerm:
            t = term
        if prevIsNum:
            t = self.numToTerm(num)
        if adding:
            if prevIsNum or prevIsTerm:
                if prevIsNum and num == 0:
                    self.invalidString = True
                    self.errMessage = '0 is not used in array'
                    return []
                array.append(t)
                t = array
            else:
                self.invalidString = True
                self.errMessage = 'String expected to continue'
                return []
        else:
            if len(array) > 1:
                t = array
        return t

    def numToTerm(self, num):
        """Convert number to term

        """
        if num == 0:
            return []
        if num == 1:
            return [0, []]
        return [[0, []]]*num

    def TtoStr(self, term):
        """Convert term to string of term

        """
        if len(term) == 0:
            return('0')
        if type(term[0]) is int:
            if term[0] == self.omega:
                level = 'ω'
            else:
                level = str(term[0])
            if self.lenTerm(term[1]) > 1:
                return 'D'+level+self.TtoStr(term[1])
            else:
                return 'D'+level+'('+self.TtoStr(term[1])+')'
        s = ''
        for t in term:
            if s == '':
                s = '('
            else:
                s += ','
            s += self.TtoStr(t)
        s += ')'
        return s

    def OTtoOrd(self, term):
        """Convert ordinal term to ordinal

        """
        # Note that it only translates OT because permutation of addition is
        # not implemented.
        if len(term) == 0:
            return('0')
        if type(term[0]) is int:
            if term[0] == self.omega:
                level = 'ω'
            else:
                level = str(term[0])
            return 'ψ'+level+'('+self.OTtoOrd(term[1])+')'
        s = ''
        for t in term:
            if s > '':
                s += '+'
            s += self.OTtoOrd(t)
        return s

    def ordToSimple(self, ord):
        """Simplify expression of ordinal using number and omega

        """
        ord = ord.replace('ψ0(0)', '1')
        ord = ord.replace('ψ0(1)', 'ω')
        ord = ord.replace('1+', 's')
        while 's' in ord:
            start = ord.find('s')
            end = start
            while ord[end+1] == 's':
                end += 1
            ord = ord[:start] + str(end - start + 2) + ord[end+2:]

        return ord

    def termIsPT(self, term):
        """Check if term is PT (Principal term)

        """
        if len(term) == 0:
            return False
        if type(term[0]) is int:
            return True
        return False

    def lenTerm(self, term):
        """Length of array of term

        """
        if self.termIsPT(term):
            return 1
        return len(term)

    def getElement(self, term, i):
        """Get i-th element of term

        """
        if self.termIsPT(term) and i == 0:
            return term
        return term[i]

    def isLessThan(self, a, b):
        """Check if a < b

        """
        # (<1) in p.200, Buchholz (1986)
        if len(b) == 0:
            return False
        if len(a) == 0:
            return True
        # (<2)
        if self.termIsPT(a) and self.termIsPT(b):
            if a[0] < b[0]:
                return True
            if a[0] == b[0] and self.isLessThan(a[1], b[1]):
                return True
            return False
        # (<3)
        for i in range(min(self.lenTerm(a), self.lenTerm(b))):
            if str(self.getElement(a, i)) != str(self.getElement(b, i)):
                return self.isLessThan(self.getElement(a, i), self.getElement(b, i))
        if self.lenTerm(a) < self.lenTerm(b):
            return True
        return False

    def checkOT3(self, u, a, b):
        """Check if G_u(a) < b for use in termIsOT function

        """
        # (G1)
        if len(a) == 0:
            return True
        # (G2)
        if not self.termIsPT(a):
            for i in range(len(a)):
                if not self.checkOT3(u, a[i], b):
                    # (OT2) checks order of array first.
                    # Therefore array is already ordered, and
                    # G_u(a_i) ≥ Teq > (a_i, ..., a_k)
                    # G_u(a) ≥ (a_0, ..., a_{i-1}, Teq)
                    # (a_0, ..., a_{i-1}, Teq) is Teq to return
                    if i > 0:
                        a = a[:i+1]
                        a[i] = self.Teq
                        self.Teq = a
                    return False
            return True
        # (G3)
        v, c = a  # a = D_v(c)
        if v < u:
            return True
        # a = D_v(c), G_u(a) = {c} ∪ G_u(c)
        # ∴ G_u(a) < b ⇔ {c} ∪ G_u(c) < b ⇔ ({c} < b)∧(G_u(c) < b)
        if self.isLessThan(b, c):  # b < c -> ￢({c} < b)
            DvLim = [v+1, []]  # ∀c(Dv(c) < DvLim)
            if self.isLessThan(DvLim, c):
                self.Teq = DvLim
                return False
            self.Teq = c
            return False
        if self.checkOT3(u, c, b):  # G_u(c) < b
            return True
        a[1] = self.Teq
        self.Teq = a
        return False

    def termIsOT(self, term):
        """Check if term is OT for use in checkOT function

        See p.201, Buchholz (1986) for detail
        """
        # (OT1)
        if len(term) == 0:
            return True
        # (OT2)
        if not self.termIsPT(term):
            # Order the array from largest to smallest
            for i in range(len(term)-1):
                if self.isLessThan(term[i], term[i+1]):
                    term[i], term[i+1] = term[i+1], term[i]
                    self.Teq = term
                    return False
            # Check every term in the array is in OT
            for i in range(len(term)):
                if not self.termIsOT(term[i]):
                    term[i] = self.Teq
                    self.Teq = term
                    return False
            return True
        # (OT3)
        v, b = term  # term = Dv(b)
        if self.termIsOT(b) and self.checkOT3(v, b, b):
            return True
        term[1] = self.Teq
        self.Teq = term
        return False

    def checkOT(self):
        """Check if term is OT

        """
        self.Teq = ''
        self.OT = ''
        self.isOT = self.termIsOT(self.T)
        return


def main():
    """Buchholz psi analyzer

    Determine if it is commandline or CGI.
    """
    import os
    if os.getenv('SCRIPT_NAME') is None:
        maincl()
    else:
        maincgi()
    return


def maincl():
    """Buchholz psi analyzer

    Invoked from command line.
    """
    import sys
    testOrdinal()  # Test if it works properly.
    if len(sys.argv) == 1:
        print('Usage: ' + sys.argv[0] + " 'ordinal'")
    else:
        analyzeOrdinal(sys.argv[1])
    return


def maincgi():
    """Buchholz psi analyzer

    Running as a CGI program.
    """
    import cgi
    # Comment out for debugging
    # import cgitb
    # cgitb.enable()
    # Write html
    print(r'''Content-Type: text/html

<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Buchholz &psi; analyzer</title>
  <link rel="stylesheet" type="text/css" href="fish.css">
</head>
<body>
<h1>Buchholz &psi; analyzer</h1>
<div style="text-align: center;
   margin: 10px 10px; padding: 8px;
   border: 5px ridge green;
   border-radius: 20px 20px 20px 20px / 20px 20px 20px 20px ;
   font-family: helvetica, sans-serif;
   background-color: #fffdfc">
<form action="psi.cgi" method="post">
  Ordinal notation <input type="text" name="text" size="50" />
  <input type="submit" />
</form>
</div>
''')
    # Get form input
    f = cgi.FieldStorage()
    a = f.getfirst('text', '')
    if len(a) > 0 and ordinal(a).errMessage != 'Invalid character':
        print('<pre>')
        analyzeOrdinal(a)
        print("</pre>")
    else:
        if len(a) > 0:
            print('<p>Invalid character was used.</p>')
        print(r'''<h2>About this program</h2>
<p>This program analyzes
<a href="https://googology.wikia.org/wiki/Buchholz%27s_function">Buchholz
&psi; function</a> defined in Buchholz (1986). When the user gives an ordinal
term a ∈ T, as defined in the reference, the program determines if a ∈ OT.
If a ∉ OT, b ∈ OT (o(a) = o(b)) is suggested. For example:
<pre>''')
        analyzeOrdinal('D1(D0(0),D1(D4(0)),D3(D0(0)))')
        print(r'''</pre>
''')
    print(r'''<h2>Input string</h2>
<p>Examples</p>
<ul>
<li>D0(D1(Dw(0)),0(0))
<li>D0(D0(D2(0)),D0(0))
<li>D2(D0(D4(0)),D3(0),D6(D3(D6(0))))
<li>D0(D3(0),D1(D2(0)),D0(0))
<li>0(1(2),w(3))
<li>0(1(2(0)),0(0))
<li>0(w,1(2(0
<li>w#3
<li>1#w
<li>ψ0(ψω(0)#1)
</ul>
<p>Rules</p>
<ul>
<li>Input a ∈ T as shown in the reference
<li>D, ψ, ' ' are neglected
<li># is regarded as ,
<li>natural numbers are analyzed
<li>w and ω are regarded as ω
<li>) is added at the end if needed
</ul>
<h2>Reference</h2>
<p>Buchholz, W. (1986): <a href="https://doi.org/10.1016/0168-0072(86)90052-7">A
   New System of Proof-Theoretic Ordinal Function.</a>
   Annals of Pure and Applied Logic, 32:195-207.</p>
<hr>
<p style="text-align: right;"><a href="{0}">{1}</a> {2} by
<a href="https://googology.wikia.org/wiki/User:Kyodaisuu">Fish</a></p>
</body>
</html>
'''.format(url, name, version))
    return


if __name__ == '__main__':
    main()
