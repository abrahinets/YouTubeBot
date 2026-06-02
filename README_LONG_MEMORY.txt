Bebryk Bot — Groq 70B + Firebase Long Memory

ВАЖЛИВО: ai_settings.json після вставки Groq API key не скидай нікому.
firebase_service_account.json також не скидай нікому.

Що робить довга пам'ять:
- у документі користувача зберігає останні 50 повідомлень/відповідей для контексту;
- у subcollection logs зберігає повний архів усіх діалогів без обрізання;
- у відповідь не відправляє весь архів, бо це швидко спалить токени, але архів у Firestore лишається.

Запуск:
1) Розпакуй архів у C:\Users\Rostyslav\Desktop\YouTubeBot
2) Встав Groq key у ai_settings.json → api_key
3) Поклади firebase_service_account.json поруч із bot.py
4) pip install -r requirements.txt
5) python bot.py --dry-run

Команди:
бот ші статус
бот пам'ять статус
