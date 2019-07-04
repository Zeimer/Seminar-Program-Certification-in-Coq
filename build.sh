#!/bin/sh

# Skrypt skopiowany z https://github.com/Zeimer/CoqBookPL

# Zrób nowego makefile'a na wypadek, gdyby pojawiły się jakieś nowe pliki .v
coq_makefile -R "." CoqBookPL -o makefile $(find . -name "*v")

# Skompiluj pliki .v - dzięki temu mamy pewność, że cały kod z książki działa poprawnie.
make

# Zbuduj wersję HTML.

# coqdoc book/*v --html -d docs generuje pliki .html z plików .v i umieszcza je w folderze docs/
# --with-footer assets/footer.html dodaje stopkę, która jest pusta
# --with-header assets/header.html dodaje nagłówek, w którym są szpiegujące analitiksy z Google'a
# --no-lib-name --lib-subtitles robi ładniejszy format tytułu dla każdego rozdziału
# --parse-comments odpowiada za to, że komentarze postaci (* ===> cośtam *) normalnie się wyświetlają
# --no-index pozbywa się indeksu (czyli spisu identyfikatorów, definicji, twierdzeń etc.)
# --toc --toc-depth 2 robi spis treści o głębokości 2
# Update 2017-02-17: opcja --utf8 została wywalona, dzięki czemu "->" wyświetla się teraz jako "->", a nie jako "→", jak poprzednio.
coqdoc Seminar.v --html -d docs                             \
       --with-footer assets/footer.html                   \
       --with-header assets/header.html                   \
       --no-lib-name --lib-subtitles                      \
       --parse-comments                                   \
       --no-index                                         \
       --toc --toc-depth 2

# Dodaj style CSS, pliki .js potrzebne nie pamiętam do czego, oraz okładkę.
cp assets/*css assets/*js docs/

# Zamień spis treści na stronę startową.
mv docs/toc.html docs/index.html

# Wywal makefile'a - po co ma zaśmiecać folder?
rm makefile makefile.conf
