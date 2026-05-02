Configuring how Alt+Tab behaves with workspaces in GNOME
========================================================

By default, Alt+Tab can cross workspace boundaries in GNOME.

To illustrate, say that you have a web browser window in workspace 1 and a
terminal emulator window in workspace 2. If you switch from workspace 1 to workspace
2 and then Alt+Tab, you'll be taken back to the browser window in workspace 1.

That's not how I personally expect Alt+Tab to work. I prefer that it switches
only among the windows in the current workspace. Fortunately, GNOME can be configured
to work just like this.

This configuration option is not exposed in the Settings app. It's not even exposed
in the Tweaks app; it's only available through :command:`gsettings` on the command
line. The magic invocation is:

.. code-block:: console

   $ gsettings set org.gnome.shell.app-switcher current-workspace-only true
   $ gsettings set org.gnome.shell.window-switcher current-workspace-only true

The setting on :code:`window-switcher` is set to true by default so maybe the second
line is not needed if you've never touched these settings on your machine, but
it cannot hurt.

The setting is declared `here`__ in the source code of GNOME. The version history leads
to discussions that contain in particular an explanation of why Alt+Tab crosses workspace
boundaries by default. What I got from it is that it was a deliberate decision
because it makes the interface more consistent from a certain point of view, but it
was also acknowledged that this point of view is not shared by everyone so the configuration
knobs were added.

__ https://gitlab.gnome.org/GNOME/gnome-shell/-/blob/b154abd6608ecd64916fdfeea70eb72e1f9686df/data/org.gnome.shell.gschema.xml.in#L310
