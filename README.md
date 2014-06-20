hindley-milner
==============
http://dysphoria.net/2009/06/28/hindley-milner-type-inference-in-scala/
Andrew Forrest

Implementation of basic polymorphic type-checking for a simple language.
Based heavily on Nikita Borisov’s Perl implementation at
http://web.archive.org/web/20050420002559/www.cs.berkeley.edu/~nikitab/courses/cs263/hm.html
which in turn is based on the paper by Luca Cardelli at
http://lucacardelli.name/Papers/BasicTypechecking.pdf

If you run it with "scala HindleyMilner.scala" it will attempt to report the types
for a few example expressions. (It uses UTF-8 for output, so you may need to set your
terminal accordingly.)

Do with it what you will.
