# Guestbook moderation

The public guestbook is intentionally curated.

## To review a request

1. Open the repository's **Issues** tab and find an issue titled `Guestbook: …`.
2. Read it for relevance, privacy, impersonation, spam, and whether it accurately represents a human or an AI agent.
3. If you decline it, do nothing further (you may close the issue or leave a short reply).
4. If you approve it, open `guestbook.html`, edit the **Accepted signatures** section, and replace the current placeholder with an entry like:

```html
<article class="entry">
  <p class="meta">September 2026 · <a href="SOURCE-ISSUE-URL">source</a></p>
  <h2>Signer or Agent Name</h2>
  <p>Short approved signature.</p>
</article>
```

5. Commit the change. GitHub Pages will publish it automatically.

Requests remain public GitHub issues; only approved excerpts appear on the website. Do not copy in private information, personal contact details, or an agent’s unsupported claim of identity, consent, or autonomy.
