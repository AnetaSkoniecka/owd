reset;

##################################################################################################
# DEKLARACJE
##################################################################################################

set SUROWCE;
set KATEGORIE;
set PRODUKTY;
set POLPRODUKTY_D;
set POLPRODUKTY_K;

param dostepnosc_surowca {s in SUROWCE};
param cena_surowca_s {s in SUROWCE};
param ilosc_polproduktu_d_na_surowiec {s in SUROWCE, d in POLPRODUKTY_D};
param przygotowalnia_przepustowosc;
param ilosc_polproduktu_k_na_polprodukt_d {d in POLPRODUKTY_D, k in POLPRODUKTY_K};
param uwodornienia_przepustowosc;
param koszt_pracy_uwodornienia;
param mozliwosc_produkcji_p_z_d {d in POLPRODUKTY_D, p in PRODUKTY};
param mozliwosc_produkcji_p_z_k {k in POLPRODUKTY_K, p in PRODUKTY};
param cena_sprzedazy_produktu_p {p in PRODUKTY};
param cena_pracy_uwodornienia;

var wykorzystanie_s {s in SUROWCE} integer >= 0;
var koszt_wykorzystania_s {s in SUROWCE} integer >= 0;
var wytworzone_polprodukty_d {d in POLPRODUKTY_D} integer >= 0;
var wytworzone_polprodukty_d_na_k {d in POLPRODUKTY_D} integer >= 0;
var wytworzone_polprodukty_d_na_p {d in POLPRODUKTY_D} integer >= 0;
var wytworzone_polprodukty_k {k in POLPRODUKTY_K} integer >= 0;
var wykorzystanie_polproduktu_k_na_p {k in POLPRODUKTY_K, p in PRODUKTY} integer >= 0;
var wykorzystanie_polproduktu_d_na_p {d in POLPRODUKTY_D, p in PRODUKTY} integer >= 0;
var wytworzone_produkty {p in PRODUKTY} integer >= 0;
var koszt_uwodornienia >= 0;
var uwodornienie_pracuje binary;
var koszt >= 0;
var dochod >= 0;

##################################################################################################
# OGRANICZENIA
##################################################################################################

#	###################
# 	dostepnosc surowca s
subject to max_wykorzystanie_s {s in SUROWCE}: dostepnosc_surowca[s] >= wykorzystanie_s[s];

#	################### *****
# 	koszt wykorzystania surowca s
subject to ile_kosztuje_wykrozystanie_s {s in SUROWCE}: koszt_wykorzystania_s[s] = wykorzystanie_s[s] * (cena_surowca_s[s] + 8);

#	###################
# 	ilosc wytworzonych polproduktow d
subject to ile_polproduktow_d {d in POLPRODUKTY_D}: wytworzone_polprodukty_d[d] = sum {s in SUROWCE} (wykorzystanie_s[s] * ilosc_polproduktu_d_na_surowiec[s, d]);

#	###################
# 	wykorzystanie przygotowalni, przerob s na d
subject to max_przygotowalnia_przepust: (sum {s in SUROWCE} wykorzystanie_s[s]) <= przygotowalnia_przepustowosc;

#	################### ?? czy napewno dobry warunek ??
# 	wykorzystanie zakladu uwodornienia, przerob d na k
subject to max_uwodornienia_przepust: (sum {d in POLPRODUKTY_D} wytworzone_polprodukty_d_na_k[d]) <= uwodornienia_przepustowosc;

#	###################
# 	wytworzone_polprodukty_d wykorzystane sa do produkcji k lub p
subject to wszystkie_wytworzone_polprodukty_d {d in POLPRODUKTY_D}: wytworzone_polprodukty_d[d] = wytworzone_polprodukty_d_na_k[d] + wytworzone_polprodukty_d_na_p[d];

#	###################
# 	ilosc wytworzonych polproduktow k
subject to ile_polproduktow_k {k in POLPRODUKTY_K}: wytworzone_polprodukty_k[k] = sum {d in POLPRODUKTY_D} (wytworzone_polprodukty_d_na_k[d] * ilosc_polproduktu_k_na_polprodukt_d[d, k]);

#	###################
# 	wykorzystanie polproduktow k na produkty
subject to jak_wykorzystano_polprodukty_k {k in POLPRODUKTY_K}: (sum {p in PRODUKTY} (wykorzystanie_polproduktu_k_na_p[k,p])) = wytworzone_polprodukty_k[k];

#	###################
# 	wykorzystanie polproduktow d na produkty
subject to jak_wykorzystano_polprodukty_d {d in POLPRODUKTY_D}: (sum {p in PRODUKTY} (wykorzystanie_polproduktu_d_na_p[d,p] * 1)) = wytworzone_polprodukty_d_na_p[d];

#	###################
# 	co z czego można produkowac
subject to produkcja_d_na_p {d in POLPRODUKTY_D, p in PRODUKTY}: wykorzystanie_polproduktu_d_na_p[d,p] <= mozliwosc_produkcji_p_z_d[d,p];
subject to produkcja_k_na_p {k in POLPRODUKTY_K, p in PRODUKTY}: wykorzystanie_polproduktu_k_na_p[k,p] <= mozliwosc_produkcji_p_z_k[k,p];

#	###################
# 	ilosc wytworzonych produktow
subject to ile_produktow_wytworzono {p in PRODUKTY}: wytworzone_produkty[p] = (sum {k in POLPRODUKTY_K} wykorzystanie_polproduktu_k_na_p[k,p]) + (sum {d in POLPRODUKTY_D} wykorzystanie_polproduktu_d_na_p[d,p]);

#	###################
# 	jaki dochod z wytworzonych produktow
subject to licz_dochod: dochod = sum {p in PRODUKTY} wytworzone_produkty[p] * cena_sprzedazy_produktu_p[p];

#	###################
# 	wyliczenie kosztu uwodornienia
subject to licz_koszt_uwodornienia: koszt_uwodornienia >= cena_pracy_uwodornienia * uwodornienie_pracuje;
subject to kiedy_uwodornienie_pracuje: 9999999 * uwodornienie_pracuje >= (sum {d in POLPRODUKTY_D}
wytworzone_polprodukty_d_na_k[d]); 

#	###################
# 	jakie koszta calkowite
subject to licz_koszt_calkowity: koszt = 
		(sum {s in SUROWCE} koszt_wykorzystania_s[s]) 		# koszt zakupy surowca ( + cena koszt przerobu *)
	+	koszt_uwodornienia 									# koszt pracy zakladu uwodornienia
	;

##################################################################################################
# FUNKCJA CELU
##################################################################################################

maximize total_zysk: dochod - koszt;

##################################################################################################
# KONFIGIURACJA
##################################################################################################

data prosty.dat;
option solver cplex;
solve;

display koszt_wykorzystania_s;
display wykorzystanie_s;
display wytworzone_polprodukty_d;
display wytworzone_polprodukty_d_na_k;
display wytworzone_polprodukty_d_na_p;
display wytworzone_polprodukty_k;
display wykorzystanie_polproduktu_k_na_p;
display wykorzystanie_polproduktu_d_na_p;
display wytworzone_produkty;
display dochod;
display koszt;
display koszt_uwodornienia;
display total_zysk;
##################################################################################################