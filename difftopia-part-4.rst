Difftopia part 4
================

This is part 4 of :doc:`my Difftopia series <the-connection-between-longest-common-subsequence-and-diff-algorithms>`
about diff algorithms. The first three parts are under the form of Software-Foundations-style Rocq files with
exercises but this one will be a web page and will have more visual elements.

Part 3 ended with the presentation of an algorithm that, for any two input lists, returns a
longest common subsequence of these two lists. But so far we haven't said much about
what longest common subsequences are good for.

Let's remedy that. If you have done software development before, you probably have seen
longest common subsequences many times. Each time you've looked at the diff of a git commit,
for example.

Let me elaborate. I'll lean on an example taken from `the GNU diffutils documentation <diffutils_>`_.
Consider the two following snippets of text:

.. _diffutils: https://www.gnu.org/software/diffutils/manual/html_node/Example-Unified.html

.. code-block:: text

   The Way that can be told of is not the eternal Way;
   The name that can be named is not the eternal name.
   The Nameless is the origin of Heaven and Earth;
   The Named is the mother of all things.
   Therefore let there always be non-being,
     so we may see their subtlety,
   And let there always be being,
     so we may see their outcome.
   The two are the same,
   But after they are produced,
     they have different names.

.. code-block:: text

   The Nameless is the origin of Heaven and Earth;
   The named is the mother of all things.

   Therefore let there always be non-being,
     so we may see their subtlety,
   And let there always be being,
     so we may see their outcome.
   The two are the same,
   But after they are produced,
     they have different names.
   They both may be called deep and profound.
   Deeper and more profound,
   The door of all subtleties!

And now consider their diff (as produced by :code:`diff -U 50`):

.. code-block:: diff

   -The Way that can be told of is not the eternal Way;
   -The name that can be named is not the eternal name.
    The Nameless is the origin of Heaven and Earth;
   -The Named is the mother of all things.
   +The named is the mother of all things.
   +
    Therefore let there always be non-being,
      so we may see their subtlety,
    And let there always be being,
      so we may see their outcome.
    The two are the same,
    But after they are produced,
      they have different names.
   +They both may be called deep and profound.
   +Deeper and more profound,
   +The door of all subtleties!

There is a longest common subsequence here: the sequence composed of the :strong:`lines
that are neither red nor green`. (Here the :code:`T` of the Rocq development is the type
of lines of text and lists are displayed top-down.)

To convince yourself that the sequence of common lines is a subsequence of the first
text sample, you can mechanically reconstruct the corresponding :code:`is_subseq`
term by reading the diff from bottop to top. Red lines correspond to applications of
:code:`subseq_skip`, gray lines to applications of :code:`subseq_take` and green lines
can just be ignored. The same goes for the second text sample if you swap the roles of
red lines and green lines.

As for the "longest" part of "longest common subsequence", it's hard to see
at a glance but I'll eat my hat if you can find a longer one. Also, the :command:`diff`
program wouldn't be very good if 

We've just seen that when you have a diff, you also have a longest common subsequence.
Before that, we gave a formal definition of longest common subsequences alongside a
verified algorithm. In the next part, we'll extend our formal treatment to diffs.

You will find the next part in the Rocq development :download:`here <Difftopia.tgz>`.
