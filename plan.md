I'm using the Sphinx documentation system. I want to write an extension that automatically creates the index file by searching the source directory for content pages. Where should I start?

That helped. Now I want to attach metadata to all source files for it to be accessible from the HTML templates. The metadata is actually going to be publication dates, but I'm interested in a generic mechanism.

I forgot to mention that I wanted to sort the source files by date before I write them to the generated index. Is it OK to modify `app.env.meta` in the handler for `builder-inited`?

Now for a templating question. My theme has the following in `footer.html`:

```
<footer>
  {%- if (theme_prev_next_buttons_location == 'bottom' or theme_prev_next_buttons_location == 'both') and (next or prev) %}
    {#- Translators: This is an ARIA section label for the footer section of the page. -#}
    <div class="rst-footer-buttons" role="navigation" aria-label="{{ _('Footer') }}">
      {%- if prev %}
        <a href="{{ prev.link|e }}" class="btn btn-neutral float-left" title="{{ prev.title|striptags|e }}" accesskey="p" rel="prev"><span class="fa fa-arrow-circle-left" aria-hidden="true"></span> {{ _('Previous') }}</a>
      {%- endif %}
      {%- if next %}
        <a href="{{ next.link|e }}" class="btn btn-neutral float-right" title="{{ next.title|striptags|e }}" accesskey="n" rel="next">{{ _('Next') }} <span class="fa fa-arrow-circle-right" aria-hidden="true"></span></a>
      {%- endif %}
    </div>
  {%- endif %}

  <hr/>

  <div role="contentinfo">
  {%- block contentinfo %}
    <p>
    {%- if show_copyright %}
      {%- if hasdoc('copyright') %}
        {%- trans path=pathto('copyright'), copyright=copyright|e %}&#169; <a href="{{ path }}">Copyright</a> {{ copyright }}.{% endtrans %}
      {%- else %}
        {%- trans copyright=copyright|e %}&#169; Copyright {{ copyright }}.{% endtrans %}
      {%- endif %}
    {%- endif %}

    {%- if build_id and build_url %}
      <span class="build">
        {#- Translators: Build is a noun, not a verb -#}
        {%- trans %}Build{% endtrans -%}
        <a href="{{ build_url }}">{{ build_id }}</a>.
      </span>
    {%- elif commit %}
      <span class="commit">
        {#- Translators: the phrase "revision" comes from Git, referring to a commit #}
        {%- trans %}Revision{% endtrans %} <code>{{ commit }}</code>.
      </span>
    {%- endif %}
    {%- if last_updated %}
      <span class="lastupdated">
        {%- trans last_updated=last_updated|e %}Last updated on {{ last_updated }}.{% endtrans %}
      </span>
    {%- endif -%}

    </p>
  {%- endblock %}
  </div>

  {% if show_sphinx %}
    {%- set sphinx_web = '<a href="https://www.sphinx-doc.org/">Sphinx</a>' %}
    {%- set readthedocs_web = '<a href="https://readthedocs.org">Read the Docs</a>'  %}
    {#- Translators: the variable "sphinx_web" is a link to the Sphinx project documentation with the text "Sphinx" #}
    {%- trans sphinx_web=sphinx_web, readthedocs_web=readthedocs_web %}Built with {{ sphinx_web }} using a{% endtrans %}
    theme derived from one
    {% trans %}provided by {{ readthedocs_web }}{% endtrans %}.
  {% endif %}

  {%- block extrafooter %} {% endblock %}

</footer>
```

URL: https://claude.ai/chat/835df8f9-9120-4f5a-819a-970793797f14
