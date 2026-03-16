#include <gtk/gtk.h>

static void
exit_cb (GSimpleAction *simple, GVariant *parameter, gpointer user_data)
{
  exit (0);
}

static void
activate (GtkApplication *app, gpointer user_data)
{
  GtkWidget *window;

  window = gtk_application_window_new (app);
  gtk_window_set_title (GTK_WINDOW (window), "Window");
  gtk_window_set_default_size (GTK_WINDOW (window), 200, 200);
  gtk_window_present (GTK_WINDOW (window));

  const GActionEntry entries[] = { { "exit", exit_cb } };

  g_action_map_add_action_entries (G_ACTION_MAP (window), entries,
                                   G_N_ELEMENTS (entries), NULL);

  const char *const accels[] = { "e", NULL };

  gtk_application_set_accels_for_action (app, "win.exit", accels);
}

int
main (int argc, char **argv)
{
  GtkApplication *app;
  int status;

  app = gtk_application_new ("org.gtk.example", G_APPLICATION_DEFAULT_FLAGS);
  g_signal_connect (app, "activate", G_CALLBACK (activate), NULL);
  status = g_application_run (G_APPLICATION (app), argc, argv);
  g_object_unref (app);

  return status;
}
