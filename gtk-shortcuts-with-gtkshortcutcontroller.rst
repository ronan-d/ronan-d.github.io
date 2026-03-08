GTK shortcuts with GtkShortcutController
========================================

I use GTK to write keyboard-driven applications. GTK is generally a good tool for this kind of applications,
but they're not the focus of the GTK documentation. This note is a supplement to the
GTK documentation dedicated to writing keyboard-driven applications.

Let me start with two markers of keyboard-driven applications:

1. There are always-active keyboard shortcuts that are not behind modifier keys. For example, in vim, ``h``
   always moves the cursor left. On the other hand, the common ``Ctrl+q`` shortcut to quit applications
   doesn't count because it has the ``Ctrl`` modifier.

2. TODO try to remember.

Accelerators
------------

I used to set up global shortcuts in GTK with "accelerators", by which I mean the following functions:

- ``gtk_application_set_accels_for_action``.
- ``g_action_map_add_action``.

On the one hand, this gets the job done. On the other hand, the fact that you use a string
to refer to the action you're setting a shortcut for is a bit awkward. I'd rather
have a typed handle to the action that's created. On top of that, there's the catch
that you can add the action either on your ``GtkApplication`` or your ``GtkApplicationWindow``,
and that you need to prepend ``app.`` or ``win.`` to the name of the action when calling
``gtk_application_set_accels_for_action``. That's pretty hard to discover by reading
the documentation.

GtkShortcutController
---------------------

I now favor using ``gtk_widget_add_controller`` on ``GtkApplicationWindow``. The
controllers I add are ``GtkShortcutController``. I make use of the possibility to choose
the propagation phase: capture or bubble depending on the situation. The accelerator
method forces the capture propagation phase.

A shortcut can be set up by adding a ``GtkShortcut`` to the ``GtkShortcutController``.
Creating a ``GtkShortcut`` requires providing an action and a trigger. For the trigger,
I often use ``GtkKeyvalTrigger``. This is a nice improvement over the accelerator method
because it does not require using the little keyword specification language,
you provide a enum value for the key and a bitmask for the modifiers.
