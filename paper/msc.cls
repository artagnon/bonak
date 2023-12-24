\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{msc}[2018/08/09 v1.0 CUP MSC LaTeX document class]
%
\newif\ifOA\global\OAfalse%
\newif\iflsans\global\lsansfalse
\newif\ifcopoddhead\global\copoddheadfalse
\newif\ifkeyedin\global\keyedinfalse
\newif\iffirstproof\global\firstprooffalse
\newif\ifrevises\global\revisesfalse
\newif\iffinals\global\finalsfalse
\newif\ifpreview\global\previewfalse
\newif\iffootlist\global\footlistfalse
\newif\iffigsizecheck\global\figsizecheckfalse
\newif\ifresearch\global\researchfalse
\newif\ifguestedit\global\guesteditfalse
\newif\ifaubreakand\global\aubreakandfalse
\newif\ifnoundrule\global\noundrulefalse
\newif\ifcombtoc\global\combtocfalse
\newif\if@twoauthors\global\@twoauthorsfalse
\newif\if@affsep\global\@affsepfalse
\newif\iflettersize\global\lettersizetrue%
\newif\iflegalsize\global\legalsizefalse%
\newif\iftabloidsize\global\tabloidsizefalse%
\newif\ifpuretex\global\puretexfalse%
\newif\ifsamjournal\global\samjournalfalse%
\newif\ifbkmerge\global\bkmergefalse%
\newif\ifcolorimage\global\colorimagefalse%
\newif\ifbwimage\global\bwimagefalse%
\newif\ifsinglepage\global\singlepagefalse
\newif\ifblankpage\global\blankpagefalse
\newif\ifrmqpage\global\rmqpagefalse
\newif\ifrevqpage\global\revqpagefalse
\newif\ifbklpage\global\bklpagefalse
\newif\ifbkfpage\global\bkfpagefalse
\newif\ifintrotag\global\introtagfalse
\newif\ifbotfig\global\botfigfalse
\newif\ifmono\global\monofalse
\newif\ifdraft\global\draftfalse
\newif\ifprint\global\printfalse
\newif\ifauthft\global\authftfalse
\newif\iflist\global\listfalse
\newif\ifcback\global\cbackfalse
\newif\ifbback\global\bbackfalse
\newif\ifunnumbered\global\unnumberedfalse
\newif\ifchapteronly\global\chapteronlyfalse
\newif\ifcontentonly\global\contentonlyfalse
\newif\ifchaptercontent\global\chaptercontentfalse
\newif\iftoc\global\tocfalse
\newif\iftwofig\global\twofigfalse
\newif\ifsidebotfig\global\sidebotfigfalse
\newif\ifsidetopfig\global\sidetopfigfalse
\newif\iflof\global\loffalse
\newif\iflot\global\lotfalse
\newif\ifnolot
\newif\ifprintcontact\global\printcontactfalse
\newif\ifdcolalignleft\global\dcolalignleftfalse
\newif\ifrefcomma\global\refcommafalse
\newif\iffigureshow\global\figureshowfalse
\newif\iftableshow\global\tableshowfalse
\newif\ifsecnumclass\global\secnumclassfalse
\newif\iflastpagewrite\global\lastpagewritefalse
\newif\ifUnNumfigure\global\UnNumfigurefalse
\newif\ifUnNumtable\global\UnNumtablefalse
\newif\ifappendix\global\appendixfalse
\newif\ifMathRoman\global\MathRomanfalse
\newif\ifMathBold\global\MathBoldfalse
\newif\ifMathBoldIT\global\MathBoldITfalse
\newif\ifremovespaces\global\removespacesfalse
\newif\iffirstpageoff\global\firstpageofffalse
\newif\ifbkpscreate\global\bkpscreatefalse
\newif\ifnomensect\global\nomensectfalse
\newif\ifitcont\global\itcontfalse
\newif\iffigcontcheck\global\figcontcheckfalse
\newif\if@display%
\newif\if@author\global\@authortrue%
\newif\if@authoremail\global\@authoremailfalse%
\newif\if@references\global\@referencesfalse%
\newif\if@sluginfo\global\@sluginfofalse%
\newif\if@namedcontent\global\@namedcontentfalse%
\newif\if@list\global\@listfalse%%
\newif\if@numberedlist\@numberedlistfalse
\newif\if@nomenclature\@nomenclaturefalse
\newif\if@algorithm\global\@algorithmfalse
\newif\if@tablefootnote\global\@tablefootnotefalse
\newif\if@appendix\global\@appendixfalse
\newif\if@firstsection\@firstsectiontrue
\newif\if@inlinealgorithm
\newif\iffigtopcap\global\figtopcapfalse
\newif\if@rot@twoside
\newif\iflandoff\global\landofffalse
\newif\if@lastviper \@lastviperfalse
\newif\ifFoottext\global\Foottextfalse
\newif\iffootdisplay\global\footdisplayfalse
\newif\ifregistermark
\newif\ifpspdfcreate\global\pspdfcreatefalse
\newif\ifrepro\reprofalse
\newif\ifddraft
\newif\ifcontact
\newif\ifprinter
\newif\ifonline\global\onlinefalse
\newif\ifcountempty\global\countemptyfalse
\newif\ifpddata\global\pddatafalse
\newif\iffloatid\global\floatidfalse
\newif\iftocfile\global\tocfilefalse
\newif\ifmathtif\global\mathtiffalse%
\newif\ifAbstract\global\Abstractfalse
\newif\ifmergexml\global\mergexmlfalse
\newif\ifnoimage\global\noimagefalse
\newif\ifSecNo\global\SecNofalse
\newif\ifbookreview\global\bookreviewfalse%%
\newif\ifnoranges\global\norangesfalse%%
\newif\ifnodoi\global\nodoifalse%%
\newif\ifnokeyword\global\nokeywordfalse%%
\newif\ifnocopyright\global\nocopyrightfalse%%
\newif\ifnocopysymb\global\nocopysymbfalse%%
\newif\ifreviewer\global\reviewerfalse%%
\newif\ifcallpaper\global\callpaperfalse%%
\newif\iftexteditor\global\texteditorfalse%%
\newif\ifeditorial\global\editorialfalse%%
\newif\ifDhead\global\Dheadfalse%%
\newif\ifEPF\global\EPFfalse%
\newif\ifmergetoc\global\mergetocfalse%
\newif\ifnoauthor\global\noauthorfalse%
\newif\ifdbleed\global\dbleedfalse%
\newif\ifsupertitle\global\supertitlefalse%
\newif\iffigsrcpresent\global\figsrcpresentfalse
\newif\ifcallforpaper\global\callforpaperfalse%
\newif\ifintexttbl\global\intexttblfalse
\newif\ifnoqrule\global\noqrulefalse
\newif\ifnoabstract\global\noabstractfalse%%
\newif\ifcorrigendum\global\corrigendumfalse%%
\newif\ifsupplementary\global\supplementaryfalse%
\newif\ifbkblurb\global\bkblurbfalse%%
\newif\ifsplissue\global\splissuefalse%
\newif\ifannouncement\global\announcementfalse%%
\newif\iferratum\global\erratumfalse
\newif\if@obituary\global\@obituaryfalse
\newif\if@unnumref\global\@unnumreftrue
\newif\if@puretex\global\@puretexfalse
\newif\if@final\@finalfalse
\newif\if@toc\global\@tocfalse
\newif\if@aa\global\@aafalse
\newif\if@rp\global\@rpfalse
\newif\if@issue\global\@issuefalse
\newif\if@ddraft\@ddraftfalse
\newif\if@editorial\@editorialfalse
\newif\if@puretex\global\@puretexfalse
\newif\if@colorinfo\global\@colorinfofalse
\newif\if@justnomen\global\@justnomenfalse
\newif\if@wfp\global\@wfpfalse
\newif\if@comm\global\@commfalse
\newif\if@figcenter\global\@figcenterfalse
\newif\if@smallformat\global\@smallformatfalse
\newif\if@cover\global\@coverfalse%
\newif\if@bwcover\global\@bwcoverfalse%
\newif\if@runonauthor
\newif\if@history\global\@historyfalse
\newif\if@corres\global\@corresfalse
\newif\if@reflink\global\@reflinkfalse
\newif\ifdhead\global\dheadfalse
\newif\ifvoltoc\global\voltocfalse
\newif\ifauthor \authorfalse%
\newif\iffloutsidemargin\floutsidemarginfalse
\newif\ifflinsidemargin\flinsidemarginfalse
\newif\ifflleftsidemargin\flleftsidemarginfalse
\newif\ifflrightsidemargin\flrightsidemarginfalse
\newif\iffloutsidetexttypewidthsep\floutsidetexttypewidthsepfalse
\newif\ifflinsidetexttypewidthsep\flinsidetexttypewidthsepfalse
\newif\ifflleftsidetexttypewidthsep\flleftsidetexttypewidthsepfalse
\newif\ifflrightsidetexttypewidthsep\flrightsidetexttypewidthsepfalse
\newif\ifExample\global\Examplefalse
\newif\ifrunon\runonfalse
\newif\if@thmdot\global\@thmdotfalse
\newif\ifswitchcols
\newif\ifauthor \authorfalse%
\newif\ifaffiliation \global\affiliationfalse%
\newif\if@oneoffnum\global\@oneoffnumfalse
\newif\ifunnumberedaffil\unnumberedaffilfalse
\newif\ifsymbolaffilcount\symbolaffilcountfalse
\newif\ifreview\global\reviewfalse
\newif\iflabelrightalign\labelrightaligntrue
\newif\iffnalpha\global\fnalphafalse
\newif\ifunnumlistitem\unnumlistitemfalse
\newif\ifFP\global\FPfalse
\newif\ifCO\global\COfalse
\newif\ifsidefigure\global\sidefigurefalse
\newif\ifrightsidefigure\global\rightsidefigurefalse
\newif\iftopcap\global\topcaptrue
\newif\ifbotcap\global\botcapfalse
\newif\ifcencap\global\cencapfalse
\newif\ifsidewaysfigure\sidewaysfigurefalse
\newif\ifmarginalfigure\marginalfigurefalse
\newif\ifTBhang\global\TBhangtrue
\newif\ifwithintabular\withintabularfalse
\newif\ifsidewaystable\sidewaystablefalse%
\newif\ifsidewbreak\sidewbreakfalse%
\newif\ifhangtab\global\hangtabfalse
\newif\ifremovetoprule\global\removetoprulefalse
\newif\ifremovebotrule\global\removebotrulefalse
\newif\ifunnumtable\unnumtablefalse
\newif\ifmarginaltable\marginaltablefalse
\newif\iftablewithshade\tablewithshadefalse
\newif\iftbsidecap\tbsidecapfalse
\newif\iftablerulebox\global\tableruleboxfalse%
\newif\ifkilltableabovespace\killtableabovespacefalse
\newif\ifnobotrule\global\nobotrulefalse%
\newif\ifnocaption\global\nocaptionfalse
\newif\ifframed\framedfalse
\newif\ifnotablenum
\newif\iftablefootnotenone\tablefootnotenonefalse
\newif\iftestbody\testbodytrue
\newif\ifbibchapter\global\bibchapterfalse
\newif\ifnumsqure\global\numsqurefalse
\newif\ifnotoc\global\notocfalse
\newif\iffirstfm\global\firstfmtrue%
\newif\iffirstbm\global\firstbmfalse%
\newif\ifstartfm\global\startfmtrue%
\newif\ifdottedfmbmcontent\dottedfmbmcontentfalse%
\newif\iffixauthorcontent\fixauthorcontentfalse%
\newif\ifswitch@CH@bkm@no\global\switch@CH@bkm@nofalse%
\newif\iffixchapcontent\fixchapcontentfalse%
\newif\ifdottedchapcontent\dottedchapcontenttrue%
\newif\ifctocfixsectioncontent\ctocfixsectioncontentfalse%
\newif\ifctocdottedsectioncontent\ctocdottedsectioncontenttrue%
\newif\ifctocfixsubsectioncontent\ctocfixsubsectioncontentfalse%
\newif\ifctocdottedsubsectioncontent\ctocdottedsubsectioncontenttrue%
\newif\iffixfigurecontent\fixfigurecontentfalse%
\newif\ifdottedfigurecontent\dottedfigurecontenttrue%
\newif\iffixtablecontent\fixtablecontentfalse%
\newif\ifdottedtablecontent\dottedtablecontenttrue%
\newif\ifremoveaux\removeauxfalse%
\newif\ifspreadlong
\newif\ifcilayout\global\cilayoutfalse
\newif\ifmath\global\mathfalse
\newif\iftoptabcaption\global\toptabcaptiontrue
\newif\ifbottabcaption\global\bottabcaptionfalse
   %
   \@twosidetrue\@mparswitchtrue

   \newcount\tempcount
   \newcount\affcount\affcount0%
   \newcount\afftempcount
   \newcount\tempaffcount
   \newcount\instcount\instcount0%
   \newcount\insttempcount
   \newcount\tempinstcount
   \newcount\deptcount\deptcount0%
   \newcount\depttempcount
   \newcount\tempdeptcount
   \newcount\streetcount\streetcount0%
   \newcount\streettempcount
   \newcount\tempstreetcount
   \newcount\citycount\citycount0%
   \newcount\citytempcount
   \newcount\tempcitycount
   \newcount\statecount\statecount0%
   \newcount\statetempcount
   \newcount\tempstatecount
   \newcount\postcodecount\postcodecount0%
   \newcount\postcodetempcount
   \newcount\temppostcodecount
   \newcount\countrycount\countrycount0%
   \newcount\countrytempcount
   \newcount\tempcountrycount
   \newcount\refvaluecount
   \newcount\temprefvaluecount
   \newcount\refvaluetempcount
   \newcount\enunheadcount
   \newcount\tempenunheadcount
   \newcount\enuntempcount
   \newcount\algheadcount
   \newcount\tempalgheadcount
   \newcount\algtempcount
   \newcount\authorcount\authorcount0%
   \newcount\tempauthorcount\tempauthorcount0%
   \newcount\authorcommacount\authorcommacount0%
   \newcount\authortempcount\authortempcount0%
   \newcount\keywordcount
   \newcount\keytempcount
   \newcount\tempkeywordcount
   \newcount\minute
   \newcount\hour
   \newcount\authorcount \authorcount0%
   \newcount\tempaffilcount
   \newcount\authorcount \authorcount0%
   \newcount\tempauthorcount \tempauthorcount0%
   \newcount\affiliationcount \affiliationcount0%
   \newcount\tempaffiliationcount \tempaffiliationcount0%
   \newcount\tempcount
   \newcount\affilcount
   \newcount\affiltempcount
   \newcount\tempaffilcount
   \newcount\membercount
   \newcount\membertempcount
   \newcount\tempmembercount
   \newcount\historycount
   \newcount\historytempcount
   \newcount\temphistorycount
   \newcount\historycount
   \newcount\historytempcount
   \newcount\temphistorycount
   \newcount\symtempcount
   \newcount\tfootcount\global\tfootcount0
   \newcount\temptfootcount%
   \newcount\tbodycount\global\tbodycount0
   \newcount\tgroupcount\tgroupcount0
   \newcount\bcount
   \newcount\ncount\ncount=1
   \newcount\ccount\ccount=1
   \newcount\acomcount
   \newcount\tempacomcount
   \newcount\acomtempcount
   \newcount\TotalCharCount\TotalCharCount0
   \newcount\seccount%
   \newcount\authcount%
   \newcount\SCOUNT
   \newcount\HCOUNT
   \newcount\fpcount
   \newcount\viper@penalty
   \newcount\AQpage\AQpage0%
   \newcount\AQlpage\AQlpage0%

   \newcounter{afrfilnote}
   \newcounter {part}
   \newcounter {chapter}
   \newcounter {HLtitle}
   \newcounter {section}
   \newcounter {subsection}[section]
   \newcounter {subsubsection}[subsection]
   \newcounter {paragraph}[subsubsection]
   \newcounter {subparagraph}[paragraph]
   \newcounter {HLsection}[HLtitle]%%%%
   \newcounter {HLsubsection}[HLsection]%%%%
   \newcounter {HLsubsubsection}[HLsubsection]%%%%
   \newcounter {HLparagraph}[HLsubsubsection]%%%%
   \newcounter {HLsubparagraph}[HLparagraph]%%%%
   \newcounter {subsubparagraph}[subparagraph]%%%%
   \newcounter {subsubsubparagraph}[subsubparagraph]%%%%
   \newcounter {HLsubsubparagraph}%[HLsubparagraph]%%%%
   \newcounter {HLsubsubsubparagraph}%[HLsubsubparagraph]%%%%
   \newcounter{ncount}
   \newcounter{figure}[chapter]
   \newcounter{table}
   \newcounter{samp}
   \newcounter{abscount}
   \newcounter{startendpage}

   \newdimen\trimwidthval
   \newdimen\trimwidthbleedval
   \newdimen\trimheightval
   \newdimen\trimheightbleedval
   \newdimen\draftrule\draftrule0pt
   \newdimen\trimrule\trimrule0pt
   \newdimen\tempdimen%
   \newdimen\normaltextheight%
   \newdimen\blindfoliodrop%
   \newdimen\enumdim%
   \newdimen\figheight%
   \newdimen\figwidth%
   \newdimen\tabledim%
   \newdimen\mathindent%
   \newdimen\emathindent%
   \newdimen\bibindent%
   \newdimen\metaleftskip\metaleftskip=0pt
   \newdimen\metarightskip\metarightskip=0pt
   \newdimen\@partialpageht
   \newdimen\storedboxheight
   \newdimen\LabelSep \LabelSep4.7pt
   \newdimen\leftmarginvii
   \newdimen\leftmarginviii
   \newdimen\leftmarginix
   \newdimen\leftmarginx
   \newdimen\enumdimwd
   \newdimen\itemleftmargin
   \newdimen\itemlabelsep
   \newdimen\descleftmargin
   \newdimen\desclabelsep
   \newdimen\figcadimen
   \newdimen\captionwidth
   \newdimen\figindent
   \newdimen\figwidthcapdimen
   \newdimen\exfigdimwd
   \newdimen\figdim
   \newdimen\tabledim%
   \newdimen\sidetskip\sidetskip=0pt%
   \newdimen\sideverticalskip\sideverticalskip=0pt
   \newdimen\tablecaptionheight
   \newdimen\sidetskip\sidetskip0pt
   \newdimen\sideverticalskip\sideverticalskip0pt
   \newdimen\tablewidth
   \newdimen\tablewidthshade
   \newdimen\fboxtablewidth
   \newdimen\tablewidth
   \newdimen\extratableheight
   \newdimen\tablebodywidth
   \newdimen\tableheight
   \newdimen\fboxgrtypewidth
   \newdimen\toprulewidth
   \newdimen\midrulewidth
   \newdimen\botrulewidth
   \newdimen\cmidrulewidth
   \newdimen\belowrulesep
   \newdimen\belowbottomsep
   \newdimen\aboverulesep
   \newdimen\abovetopsep
   \newdimen\cmidrulesep
   \newdimen\cmidrulekern
   \newdimen\defaultaddspace
   \newdimen\@thisrulewidth
   \newdimen\foot@parindent
   \newdimen\ptdraftrule
   \newdimen\ptdraftrule
   \newdimen\temptextheight
   \newdimen\bibindent
   \newdimen\bibleftmargin
   \newdimen\bibitemsep
   \newdimen\bibparsep
   \newdimen\bibtext
   \newdimen\biblabelsep
   \newdimen\bibleftmargini
   \newdimen\chapwidth%
   \newdimen\secnwidth%
   \newdimen\subsecnwidth%
   \newdimen\subsubsecnwidth%
   \newdimen\pldim%
   \newdimen\authorcontentwidth%
   \newdimen\@ctocsecmaxnumdim%
   \newdimen\ctocsecnwidth%
   \newdimen\@secmaxnumdim%
   \newdimen\secnwidth%
   \newdimen\@ctocsubsecmaxnumdim%
   \newdimen\ctocsubsecnwidth%
   \newdimen\@subsecmaxnumdim%
   \newdimen\subsecnwidth%
   \newdimen\@figuremaxnumdim%
   \newdimen\figurecontwidth%
   \newdimen\@tablemaxnumdim%
   \newdimen\tablecontwidth%
   \newdimen\tempdim
   \newdimen\presentfigwidth
   \newdimen\oldfigwidth
   \newdimen\remainingtextwidth
   \newdimen\letterwidth%
   \newdimen\letterheight%
   \newdimen\legalwidth%
   \newdimen\legalheight%
   \newdimen\tabloidwidth%
   \newdimen\tabloidheight%
   \newdimen\@tempdima%%
   \newdimen\@tempdimb%%
   \newdimen\@tempdimc%%
   \newdimen\@tempdimd%%
   \newdimen\@tempdime%%
   \newdimen\deflistmaxskip
   \newdimen\deflistskip%
   \newdimen\myskip%
   \newdimen\ht@viper

   \newbox\hisbox
   \newbox\tempbox%
   \newbox\abstractbox%
   \newbox\store@outputbox
   \newbox\keywordbox
   \newbox\subbox
   \newbox\tabimagebox
   \newbox\citybox
   \newbox\tabbox
   \newbox\tabnotebox
   \newbox\tablefootbox
   \newbox\statebox
   \newbox\pscodebox
   \newbox\countrybox
   \newbox\addlinebox
   \newbox\instbox
   \newbox\instnamebox
   \newbox\deptbox
   \newbox\zipbox
   \newbox\provincebox
   \newbox\phonebox
   \newbox\faxbox
   \newbox\deflistbox
   \newbox\boxBibH
   \newbox\onlinefibox
   \newbox\onlinefiibox
   \newbox\v@aaa
   \newbox\v@ccc
   \newbox\authrun
   \newbox\plainCOPbox%
   \newbox\colorCOPbox%
   \newbox\chap@tempbox%
   \newbox\tempabox
   \newbox\figcapbox
   \newbox\figtempbox
   \newbox\tabcapbox
   \newbox\tablefootbox
   \newbox\temptbox
   \newbox\tempttbox
   \newbox\temptttbox
   \newbox\tempttttbox
   \newbox\tabletempboxsecond
   \newbox\tabletempboxthird
   \newbox\boxcont

   \newskip\normalbaselineskip%
   \newskip\tableleftskip%
   \newskip\tablerightskip%
   \newskip\tabnoteleftskip%
   \newskip\tabnoterightskip%
   \newskip\colmargin
   \newskip\texttypewidthsep
   \newskip\authorbelowskip
   \newskip\headlineindent
   \newskip\instindent
   \newskip\topsepi
   \newskip\topsepii
   \newskip\topsepiii
   \newskip\topsepiv
   \newskip\topsepv
   \newskip\topsepvi
   \newskip\topsepvii
   \newskip\topsepviii
   \newskip\topsepix
   \newskip\topsepx
   \newskip\itemsepi
   \newskip\itemsepii
   \newskip\itemsepiii
   \newskip\itemsepiv
   \newskip\itemsepv
   \newskip\itemsepvi
   \newskip\itemsepvii
   \newskip\itemsepviii
   \newskip\itemsepix
   \newskip\itemsepx
   \newskip\listtextleftmargin
   \newskip\listtextleftmarginii
   \newskip\listtextleftmarginiii
   \newskip\listtextleftmarginiv
   \newskip\listtextleftmarginv
   \newskip\listtextleftmarginvi
   \newskip\listtextleftmarginvii
   \newskip\listtextleftmarginviii
   \newskip\listtextleftmarginix
   \newskip\listtextleftmarginx
   \newskip\listtextrightmargin
   \newskip\listlabelleftskip
   \newskip\listlabelleftskipii
   \newskip\listlabelleftskipiii
   \newskip\listlabelleftskipiv
   \newskip\listlabelleftskipv
   \newskip\listlabelleftskipvi
   \newskip\listlabelleftskipvii
   \newskip\listlabelleftskipviii
   \newskip\listlabelleftskipix
   \newskip\listlabelleftskipx
   \newskip\abovelistskipi
   \newskip\belowlistskipi
   \newskip\abovelistskipii
   \newskip\belowlistskipii
   \newskip\abovelistskipiii
   \newskip\belowlistskipiii
   \newskip\abovelistskipiv
   \newskip\belowlistskipiv
   \newskip\abovelistskipv
   \newskip\belowlistskipv
   \newskip\abovelistskipvi
   \newskip\belowlistskipvi
   \newskip\abovelistskipvii
   \newskip\belowlistskipvii
   \newskip\abovelistskipviii
   \newskip\belowlistskipviii
   \newskip\abovelistskipix
   \newskip\belowlistskipix
   \newskip\abovelistskipx
   \newskip\belowlistskipx
   \newskip\labelsepi
   \newskip\labelsepii
   \newskip\labelsepiii
   \newskip\labelsepiv
   \newskip\labelsepv
   \newskip\labelsepvi
   \newskip\labelsepvii
   \newskip\labelsepviii
   \newskip\labelsepix
   \newskip\labelsepx
   \newskip\unnumlistitemindent
   \newskip\unnumlisttextskip
   \newskip\figcaptionleftskip
   \newskip\figcaptionrightskip
   \newskip\figleftskip
   \newskip\figrightskip
   \newskip\adjustskip
   \newskip\sidetskip\sidetskip=0pt
   \newskip\sideverticalskip\sideverticalskip=0pt
   \newskip\fignumcapsep\fignumcapsep=3pt
   \newskip\figcapdescsep\figcapdescsep=2.5pt
   \newskip\tableleftskip%
   \newskip\tablerightskip%
   \newskip\tablecapleftskip%
   \newskip\tablecaprightskip%
   \newskip\sideverticalskip
   \newskip\sidetskip
   \newskip\addtotablewidth
   \newskip\tablenumcapsep
   \newskip\tablefootleftskip
   \newskip\tablefootrightskip
   \newskip\manshowtfootskip
   \newskip\footnoteabovespace
   \newskip\fixfmbmcontentwidth
   \newskip\fixauthorcontentwidth
   \newskip\fixchapcontentwidth
   \newskip\enspacechapcontentwidth
   \newskip\ctocfixsectioncontentwidth
   \newskip\ctocenspacesectioncontentwidth%
   \newskip\ctocfixsubsectioncontentwidth
   \newskip\ctocenspacesubsectioncontentwidth%
   \newskip\enspacefigurecontentwidth
   \newskip\fixfigurecontentwidth
   \newskip\fixtablecontentwidth
   \newskip\enspacetablecontentwidth
   \newskip\@mathmargin
   \newskip\verbatimindent
   \newskip\CRskip

   \newlength\subtitleval
   \newlength\abovecaptionskip
   \newlength\belowcaptionskip
   \newlength\belowtabcaptionskip
   \newlength\trimwidth%
   \newlength\trimheight%
   \newlength\typewidth%
   \newlength\typeheight%
   %
   \newtoks\authorrunning
   \newbox\titrun
   \newtoks\titlerunning
   \newtoks\tocauthor
   \newtoks\toctitle
   \newtoks\CharCounttoks

   \DeclareOption{reviewer}{\global\reviewertrue}
   \DeclareOption{noundrule}{\global\noundruletrue}
   \DeclareOption{callforpaper}{\global\callforpapertrue}
   \DeclareOption{EPF}{\global\EPFtrue}
   \DeclareOption{pdfcreate}{\global\pspdfcreatetrue}%
   \DeclareOption{lettersize}{\lettersizetrue\legalsizefalse\tabloidsizefalse}%
   \DeclareOption{legalsize}{\lettersizefalse\legalsizetrue\tabloidsizefalse}%
   \DeclareOption{tabloidsize}{\lettersizefalse\legalsizefalse\tabloidsizetrue}%
   \DeclareOption{registermark}{\registermarktrue}
   \DeclareOption{keyedin}{\keyedintrue}
   \DeclareOption{combtoc}{\combtoctrue}
   \DeclareOption{dbleed}{\global\dbleedtrue}
   \DeclareOption{supertitle}{\global\supertitletrue}
   \DeclareOption{bkmerge}{\global\bkmergetrue}
   \DeclareOption{fp}{\global\firstprooftrue}
   \DeclareOption{guestedit}{\global\guestedittrue}
   \DeclareOption{research}{\global\researchtrue}
   \DeclareOption{revises}{\global\revisestrue}
   \DeclareOption{finals}{\global\finalstrue\global\noquerytrue}
   \DeclareOption{webpdf}{\global\onlinetrue\global\noquerytrue\global\figsizechecktrue}
   \DeclareOption{colorimage}{\global\colorimagetrue\global\bwimagetrue}
   \DeclareOption{bwimage}{\global\bwimagetrue}
   \DeclareOption{preview}{\global\previewtrue\global\onlinetrue\global\noquerytrue}
   \DeclareOption{ELD}{\global\onlinetrue\global\noquerytrue}
   \DeclareOption{repro}{\reprotrue}
   \DeclareOption{noquery}{\global\noquerytrue}
   \DeclareOption{countempty}{\countemptytrue}
   \DeclareOption{draft}{\setlength\overfullrule{5pt}\draftrule.25pt\drafttrue\global\floatidtrue}
   \DeclareOption{ddraft}{\setlength\overfullrule{5pt}\draftrule.25pt\drafttrue}
   \DeclareOption{online}{\global\onlinetrue}
   \DeclareOption{final}{\setlength\overfullrule{0pt}}
   \DeclareOption{contact}{\setlength\overfullrule{0pt}\contacttrue}
   \DeclareOption{printer}{\setlength\overfullrule{0pt}\trimrule0pt\printertrue}
   \DeclareOption{purexml}{\global\puretexfalse}
   \DeclareOption{puretex}{\global\puretextrue}
   \DeclareOption{merge}{\global\tocfiletrue}
   \DeclareOption{mathtif}{\global\mathtiftrue\global\puretextrue}
   \DeclareOption{bookreview}{\global\bookreviewtrue}
   \DeclareOption{noranges}{\global\norangestrue}
   \DeclareOption{nodoi}{\global\nodoitrue}
   \DeclareOption{OA}{\global\OAtrue}
   \DeclareOption{nokeyword}{\global\nokeywordtrue}
   \DeclareOption{nocopyright}{\global\nocopyrighttrue}
   \DeclareOption{nocopysymb}{\global\nocopysymbtrue}
   \DeclareOption{singlepage}{\global\singlepagetrue}
   \DeclareOption{callpaper}{\global\callpapertrue}
   \DeclareOption{texteditor}{\global\texteditortrue}
   \DeclareOption{editorial}{\global\editorialtrue}
   \DeclareOption{mergetoc}{\global\mergetoctrue}
   \DeclareOption{noauthor}{\global\noauthortrue}
   \DeclareOption{dhead}{\global\dheadtrue}
   \DeclareOption{noabstract}{\global\noabstracttrue}
   \DeclareOption{corrigendum}{\global\corrigendumtrue}
   \DeclareOption{supplementary}{\global\supplementarytrue}
   \DeclareOption{bkblurb}{\global\bkblurbtrue}
   \DeclareOption{splissue}{\global\splissuetrue}
   \DeclareOption{announcement}{\global\announcementtrue}
   \DeclareOption{voltoc}{\global\voltoctrue}
   \DeclareOption{erratum}{\global\erratumtrue}

   \ExecuteOptions{online}
   \ProcessOptions

   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%Standard Packages

   \usepackage{amsthm}
   \usepackage{soul}
   \usepackage{calc}
   \usepackage{xcolor}

   \renewcommand{\rmdefault}{ptm}%
   \renewcommand{\sfdefault}{phv}%
   \usepackage{mathptmx}
   \definecolor{shadecolor}{cmyk}{0,0,0,.12}
   \definecolor{absshadecolor}{cmyk}{0,0,0,.12}
   \thm@bodyfont{}
   \thm@headfont{\itshape}

   \usepackage{framed}

   \newcommand\contentsname{Contents}
   \newcommand\abstractname{Abstract}
   \newcommand\keywordname{Keywords}
   \newcommand\listfigurename{List of Figures}
   \newcommand\listtablename{List of Tables}
   \newcommand\bibname{References}
   \newcommand\indexname{Index}
   \newcommand\figurename{Figure}
   \newcommand\tablename{Table}
   \newcommand\partname{Part}
   \newcommand\chaptername{Chapter}
   \newcommand\appendixname{Appendix}
   \newcommand\ackname{Acknowledgements}
   %
   \newcommand\today{\ifcase\month\or
         January\or February\or March\or April\or May\or June\or
         July\or August\or September\or October\or November\or December\fi
      \space\number\day, \number\year}
   %

   \def\currenttime{%
      \minute\time
      \hour\minute
      \divide\hour60
      \the\hour:\multiply\hour60\advance\minute-\hour\the\minute}
   %
   %\def\jobtag{\@currname\ {\bf\uppercase{Sample Elements for Quick Reference}}}%%
   %\def\jobtag{{\bf LaTeX Sample Elements for Quick Reference}}%%
   %\def\@pushfilename{%
   %  \xdef\@currnamestack{%
   %    {\@currname}%
   %    {\@currext}%
   %    {\the\catcode`\@}%
   %    \@currnamestack}}%
   %\@onlypreamble\@pushfilename%
   %\@pushfilename%
   %
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% End Boxes & Dimensions %%%%%%%%%%%%%%%%%
   %
   \def\mdash{\unskip~--\ \ignorespaces}
   %
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Fonts %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% Credit Line font
   \def\psplainfont{\fontsize{7}{7}\selectfont}
   \def\psplainfootfont{\fontsize{7}{7}\selectfont}
   \def\pscrfont{\fontfamily{\sfdefault}\fontsize{7.25}{7.725}\selectfont}
   \def\pscpfont{\psplainfont}
   %% headings
   \def\rhfont{\fontsize{9.5}{10.5}\selectfont}
   \def\rrhfont{\fontsize{9.5}{10.5}\selectfont\itshape}
   \def\foliofont{\fontsize{9.5}{10.5}\selectfont}
   \def\dropfoliofont{\foliofont}
   \def\jvolfont{\fontfamily{\sfdefault}\fontsize{10}{10}\bfseries\selectfont}
   %% part
   \def\PNfont{\fontsize{50}{50}\bfseries\selectfont\leftskip0pt plus1fill\rightskip-10pc plus1fill}
   \def\PTfont{\fontsize{32}{38}\bfseries\selectfont\leftskip0pt plus1fill\rightskip-10pc plus1fill}%\leftskip.5pc plus1fill\rightskip.5pc plus1fill}
   \def\PSTfont{\fontsize{13}{15}\bfseries\selectfont}%\leftskip.5pc plus1fill\rightskip.5pc plus1fill}
   %% chapter
   \def\keywordfont{\fontsize{8}{10}\selectfont}
   \def\authorfont{\fontsize{10}{12}\selectfont}
   \def\continuedfont{\fontfamily{\sfdefault}\fontsize{8}{8}\itshape\selectfont}
   %% section
   \def\sectionfont{%
      \ifAbstract%
         \fontsize{9.25}{11}\fontfamily{\sfdefault}\selectfont\bfseries\rightskip0pt plus1fill%
      \else%
         \fontsize{10.5}{11}\fontfamily{\sfdefault}\selectfont\bfseries\rightskip0pt plus1fill%
      \fi}%
   \def\subsectionfont{\fontsize{9.5}{11}\fontfamily{\sfdefault}\selectfont\bfseries\itshape\rightskip0pt plus1fill}
   \def\subsubsectionfont{\fontsize{9.5}{11}\fontfamily{\sfdefault}\selectfont\itshape}
   \def\paragraphfont{\fontsize{9.5}{11}\selectfont\bfseries}%
   \def\subparagraphfont{}%
   \def\subsubparagraphfont{}%
   %
   \def\sectionnumfont{\sectionfont}
   \def\subsectionnumfont{\subsectionfont}
   %
   %% figure
   \def\figcaptionfont{\fontfamily{\sfdefault}\fontsize{7.75}{9.7}\selectfont}
   \def\figcaptiondescfont{\fontfamily{\sfdefault}\fontsize{7}{9}\selectfont\leftskip0pt plus1fill\rightskip0pt plus1fill}
   \def\figcaptionnumfont{\fontsize{7.75}{9}\fontfamily{\sfdefault}\fontseries{sb}\fontshape{n}\selectfont}
   %% TABLE
   \def\multilistfont{\fontsize{8.5}{10}\selectfont\leftskip\tableleftskip\rightskip\tablerightskip}%
   \def\multilistheadfont{\fontsize{8.5}{10}\bfseries\selectfont\leftskip\tableleftskip\rightskip\tablerightskip}%
   \def\tablefont{\fontfamily{\sfdefault}\fontsize{7.75}{9}\selectfont}%
   \def\tablecaptionfont{\fontfamily{\sfdefault}\fontsize{7.75}{9}\selectfont}%
   \def\tablecaptwofont{\fontfamily{\sfdefault}\fontsize{7.8}{9}\selectfont}%
   \def\tablecaptionnumfont{\fontsize{7.75}{9}\fontfamily{\sfdefault}\fontseries{sb}\fontshape{n}\selectfont}%
   \def\TCHfont{\fontfamily{\sfdefault}\fontsize{7.5}{9}\selectfont}%
   \def\TSCHfont{}%
   \def\tabnotefont{\fontfamily{\sfdefault}\fontsize{6.51}{8}\selectfont}% use plus 1fill if needed
   %% Long-Table
   \def\LTtablecaptionfont{\fontfamily{\sfdefault}\fontsize{7.5}{9}\selectfont}%
   \def\LTtablenotefont{\fontfamily{\sfdefault}\fontsize{7.5}{9}\selectfont}%
   %% BM
   \def\indexfont{\footnotesize\raggedright}
   %
   \def\listfont{}
   \def\listdevicefont{}
   \def\extractfont{\leftskip2pc\rightskip\leftskip}
   %
   %
   \def\supertitlefont{\fontsize{16}{18}\bfseries\selectfont\centering\mathversion{bold}}
   \def\supertitleitfont{\fontsize{18}{20}\itshape\selectfont\centering\mathversion{normal}}
   \def\Dheadeditorfont{\fontsize{14}{16}\itshape\selectfont\centering\mathversion{normal}}
   %
   \def\sixtnptfont{\fontsize{16}{20}\bfseries\selectfont}
   \def\twlptfont{\fontsize{12}{12}\selectfont}
   \def\twlveptfont{\fontsize{12}{14}\selectfont}
   \def\twlbptfont{\fontsize{12}{12}\bfseries\selectfont}
   \def\eightnfont{\fontsize{18}{20}\bfseries\selectfont}
   \def\fortnfont{\fontsize{14}{16}\bfseries\selectfont}
   \def\fortnrfont{\fontsize{14}{16}\selectfont}
   \def\tenptfont{\fontsize{10}{10}\bfseries\selectfont}
   \def\nineptfont{\fontsize{9}{9}\selectfont}
   \def\ninetenfont{\fontsize{9}{10}\selectfont}
   \def\ninehptfont{\fontsize{8.7}{9}\selectfont}
   \def\eightptfont{\fontsize{8}{8}\selectfont}
   \def\eighthptfont{\fontsize{8.5}{10}\bfseries\selectfont}
   \def\sevenptfont{\fontsize{7}{8}\selectfont}
   \def\sevenhptfont{\fontsize{7.5}{8.5}\selectfont}
   \def\sixptfont{\fontsize{6}{7}\selectfont}
   \def\sixhptfont{\fontsize{6.5}{8}\selectfont}
   \def\sixedfont{\fontsize{6}{7}\selectfont\leftskip12pt\rightskip0pt plus1fill}
   \def\sixhedfont{\fontsize{5.7}{7}\selectfont\leftskip12pt\rightskip0pt plus1fill}
   \def\sixfont{\fontsize{6}{7}\selectfont}
   \def\sevenaufont{\fontsize{7}{7}\itshape\selectfont}
   \def\historyfont{\fontsize{8}{10}\selectfont}
   \def\titlefont{\fontsize{16}{18}\fontfamily{\sfdefault}\fontseries{sb}\fontshape{n}\selectfont}
   \def\artitfont{\fontsize{8.4}{10.5}\fontfamily{\sfdefault}\fontseries{sb}\fontshape{n}\selectfont}
   \def\corresfont{\fontsize{8}{10}\selectfont}
   \def\coreheadfont{\fontsize{7}{9}\selectfont\bfseries}
   \def\subtitlefont{\fontsize{10}{12}\selectfont\itshape\centering}
   \def\keyfont{\fontsize{8}{10}\selectfont}
   \def\keyheadfont{\fontsize{8}{10}\selectfont\bfseries}
   \def\absfont{\fontsize{9}{11}\selectfont}
   \def\acknowfont{\fontsize{7}{9}\selectfont}
   \def\headifont{\fontsize{10}{12}\fontfamily{\sfdefault}\selectfont\leftskip0pt plus1fill\rightskip0pt plus1fill}
   \def\refheadfont#1{#1}
   \def\affilfont{\fontsize{8}{10}\selectfont}
   %
   %%%%%%%%%%%%%%%%%%%%%%%%% Fonts %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   \def\colorone{\special{color push cmyk 0.8 0.3 0.1 0}}%1
   \def\colortwo{\special{color push cmyk 0.70 0 0.05 0.25}}%2
   \def\colorthree{\special{color push cmyk 0.20 0.60 1.0 0}}%3
   \def\colorfour{\special{color push cmyk 0 0 0.35 0}}%4%
   \def\colorfive{\special{color push cmyk 1.0 0 0 0.30}}%5
   \def\colorsix{\special{color push cmyk 0 0.15 0.60 0.05}}%6
   \def\colorseven{\special{color push cmyk 0 1.0 0 0.40}}%7
   \def\coloreight{\special{color push cmyk 0.80 0 0.70 0.35}}%8
   \def\colornine{\special{color push cmyk 0.20 0 0.20 0.05}}%9
   \def\colorten{\special{color push cmyk 0 1.0 1.0 0.60}}%10
   \def\coloreleven{\special{color push cmyk 0.25 0 0.95 0.35}}%11
   \def\colortwelve{\special{color push cmyk 1.0 0 0.35 0}}%12
   \def\colorthirteen{\special{color push cmyk 0.15 0 0 0}}%13%
   \def\colorfourteen{\special{color push cmyk 0 0 0.05 0.05}}%14
   \def\colorfifteen{\special{color push cmyk 0 0 0.30 0.20}}%15%
   \def\colorsixteen{\special{color push cmyk 0.50 0 0 0}}%16
   \def\colorseventeen{\special{color push cmyk 0 0 0.12 0.08}}%17
   \def\coloreighteen{\special{color push cmyk 0 0.30 1.0 0.20}}%18
   %
   \def\magentahundred{\special{color push cmyk 0 1.0 0 0}}%
   \def\cyanhundred{\special{color push cmyk 1.0 0 0 0}}%
   \def\cyanten{\special{color push cmyk 0.10 0 0 0}}%
   \def\colorfourtenp{\special{color push cmyk 0 0 0.10 0}}%4%
   \def\coloreighteentenp{\special{color push cmyk 0 0.03 0.10 0.02}}%18
   \def\coloreighteenfiftyp{\special{color push cmyk 0 0.15 0.50 0.10}}%18
   \def\colorseventenp{\special{color push cmyk 0 0.1 0 0.04}}%7
   \def\colorsevenfiftyp{\special{color push cmyk 0 0.8 0 0.30}}%7
   \def\coloreleventenp{\special{color push cmyk 0.025 0 0.095 0.035}}%11
   \def\colorninetenp{\special{color push cmyk 0.05 0 0.05 0.010}}%9
   \def\singlepagelabel{\global\singlepagetrue}
   %
   \def\endmark{}
   %
   \def\spreadout#1{%
      \gdef\temp{#1}%
      \dimen0 = \spreadoutfactor pt
      \ifdim\dimen0=\z@\temp\else                            % If the spreadoutfactor
         \expandafter\dospreadout\temp\endmark\kern-\dimen0\fi} % is zero, then we can use kern or hskip
   %                                                        % with the title etc. Suppressed the extra space
   %                                                        % after spreadout.
   \def\dospreadout{%
      \afterassignment\findospreadout
      \let\next= }
   %
   \def\findospreadout{%
      \ifx\next\endmark
         \let\nextaction = \relax
      \else
         \let\nextaction = \dospreadout
         \next
         \kern\dimen0
      \fi
      \nextaction}
   %
   %
   \def\@xipt{11}
   \def\@xvpt{15}
   \def\@xviiipt{18}
   \def\@xxivpt{24}
   %
   %\normalbaselineskip12\p@
   %
   \renewcommand\normalsize{%
      \@setfontsize\normalsize{10.25}{11.75}
      \abovedisplayskip5.5\p@ plus1pt minus1pt
      \abovedisplayshortskip\abovedisplayskip
      \belowdisplayshortskip\abovedisplayskip
      \belowdisplayskip \abovedisplayskip
      \let\@listi\@listI}
   \normalsize
   %
   \newcommand\small{%
      \@setfontsize\small{8.5}{10}%
      \abovedisplayskip8.5\p@ plus1pt minus1pt
      \abovedisplayshortskip\abovedisplayskip
      \belowdisplayshortskip\abovedisplayskip
      \belowdisplayskip \abovedisplayskip
      \setSmallDelims
   }
   %
   \def\setSmallDelims{%
      \def\big##1{{\hbox{$\left##1\vbox to7.5\p@{}\right.\n@space$}}}%
      \def\Big##1{{\hbox{$\left##1\vbox to10.5\p@{}\right.\n@space$}}}%
      \def\bigg##1{{\hbox{$\left##1\vbox to13.5\p@{}\right.\n@space$}}}%
      \def\Bigg##1{{\hbox{$\left##1\vbox to16.5\p@{}\right.\n@space$}}}%
      \def\biggg##1{{\hbox{$\left##1\vbox to19.5\p@{}\right.\n@space$}}}%
      \def\Biggg##1{{\hbox{$\left##1\vbox to22.5\p@{}\right.\n@space$}}}%
   }
   %
   \newcommand\footnotesize{%
      \@setfontsize\footnotesize\@viiipt{10}%
      \abovedisplayskip 4.5\p@ \@plus2\p@ \@minus4\p@
      \abovedisplayshortskip \z@ \@plus\p@
      \belowdisplayshortskip 3\p@ \@plus\p@ \@minus2\p@
      \def\@listi{\leftmargin\leftmargini
         \topsep 3\p@ \@plus\p@ \@minus\p@
         \parsep 2\p@ \@plus\p@ \@minus\p@
         \itemsep \parsep}%
      \belowdisplayskip \abovedisplayskip
      \setFootnotesizeDelims}
   %
   \def\setFootnotesizeDelims{%
      \def\big##1{{\hbox{$\left##1\vbox to6.5\p@{}\right.\n@space$}}}%
      \def\Big##1{{\hbox{$\left##1\vbox to9.5\p@{}\right.\n@space$}}}%
      \def\bigg##1{{\hbox{$\left##1\vbox to12.5\p@{}\right.\n@space$}}}%
      \def\Bigg##1{{\hbox{$\left##1\vbox to15.5\p@{}\right.\n@space$}}}%
      \def\biggg##1{{\hbox{$\left##1\vbox to18.5\p@{}\right.\n@space$}}}%
      \def\Biggg##1{{\hbox{$\left##1\vbox to21.5\p@{}\right.\n@space$}}}%
   }
   %
   \newcommand\scriptsize{\@setfontsize\scriptsize\@vipt\@viipt}
   \newcommand\tiny{\@setfontsize\tiny\@vpt\@vipt}
   \newcommand\large{\@setfontsize\large\@xiipt{14}}
   \newcommand\Large{\@setfontsize\Large\@xivpt{18}}
   \newcommand\LARGE{\@setfontsize\LARGE\@xviipt{22}}
   \newcommand\huge{\@setfontsize\huge\@xxpt{25}}
   \newcommand\Huge{\@setfontsize\Huge\@xxvpt{30}}
   %
   \DeclareOldFontCommand{\rm}{\normalfont\rmfamily}{\mathrm}
   \DeclareOldFontCommand{\sf}{\normalfont\sffamily}{\mathsf}
   \DeclareOldFontCommand{\tt}{\normalfont\ttfamily}{\mathtt}
   \DeclareOldFontCommand{\bf}{\normalfont\bfseries}{\mathbf}
   \DeclareOldFontCommand{\it}{\normalfont\itshape}{\mathit}
   \DeclareOldFontCommand{\sl}{\normalfont\slshape}{\@nomath\sl}
   \DeclareOldFontCommand{\sc}{\normalfont\scshape}{\@nomath\sc}
   \DeclareOldFontCommand{\bi}{\bfseries\itshape}{\bfseries\itshape}
   %
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Parameters %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %
   \colmargin=0pc
   \texttypewidthsep=0pc
   %
   \setlength\trimwidth{6.85in}%
   \setlength\trimheight{9.72in}%
   %
   \setlength\textwidth{398.2pt}%
   \setlength\textheight{51\baselineskip}%
   \setlength\normaltextheight{\textheight}%

   \setlength\typeheight{\textheight}%
   \setlength\typewidth{\textwidth}%

   \setlength\headheight{12\p@}
   \setlength\headsep   {.272in}
   \setlength\topskip   {10\p@}
   \setlength\footskip{.35in}
   \setlength\maxdepth{.5\topskip}
   %
   \setlength\topmargin{40.1pt}%
   \setlength\oddsidemargin{43.2pt}%
   \setlength\evensidemargin{54pt}%
   %
   \blindfoliodrop\trimheight
   \advance\blindfoliodrop-\typeheight
   \advance\blindfoliodrop-\topmargin
   \advance\blindfoliodrop-\footskip
   \advance\blindfoliodrop18pt
   %
   \setlength\parindent{12pt}
   %
   \setlength\marginparwidth {.75in}
   \setlength\marginparsep{6\p@}
   \setlength\marginparpush{5\p@}
   %
   \setlength\footnotesep{\z@}
   \setlength{\skip\footins}{11\p@ \@plus 1\p@ \@minus 1\p@}% change + based on FN font height
   \skip\@mpfootins = \skip\footins
   %
   \setlength\floatsep    {5\p@ \@plus 2\p@ \@minus 2\p@}
   \setlength\textfloatsep{11\p@ \@plus 2\p@ \@minus 4\p@}
   \setlength\intextsep   {12\p@ \@plus 2\p@ \@minus 2\p@}
   \setlength\dblfloatsep    {5\p@ \@plus 2\p@ \@minus 2\p@}
   \setlength\dbltextfloatsep{11\p@ \@plus 2\p@ \@minus 4\p@}
   \setlength\@fptop{0\p@}
   \setlength\@fpsep{8\p@ \@plus 1fil}
   \setlength\@fpbot{0\p@ \@plus 1fil}
   \setlength\@dblfptop{0\p@}
   \setlength\@dblfpsep{8\p@ \@plus 1fil}
   \setlength\@dblfpbot{0\p@ \@plus 1fil}
   %
   \setlength\partopsep{0pt}
   \setlength\lineskip{1\p@}% check if it can be flexible
   \setlength\normallineskip{1\p@}%
   \renewcommand\baselinestretch{}
   \setlength\parskip{\z@}%{0\p@ \@plus \p@}
   \@lowpenalty   51
   \@medpenalty  151
   \@highpenalty 301
   %
   \@beginparpenalty -\@lowpenalty
   \@endparpenalty   -\@lowpenalty
   \@itempenalty     -\@lowpenalty
   %
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% End Parameters %%%%%%%%%%%%%%%%%%%%%%%%%
   %
   \def\mycolor#1{#1\special{color pop}}
   %
   \def\cyan{\special{color push cmyk 1.0 0 0 0}}
   \def\magenta{\special{color push cmyk 0 1.0 0 0}}
   %%
   \def\grayten{\special{color push cmyk 0 0 0 .10}}
   %
   \def\@addmarginpar{\@next\@marbox\@currlist{\@cons\@freelist\@marbox
         \@cons\@freelist\@currbox}\@latexbug\@tempcnta\@ne
      \if@twocolumn
         \if@firstcolumn \@tempcnta\m@ne \fi
      \else
         \if@mparswitch
            \ifodd\c@page \else\@tempcnta\m@ne \fi
         \fi
         \if@reversemargin \@tempcnta -\@tempcnta \fi
      \fi
      \ifnum\@tempcnta <\z@  \global\setbox\@marbox\box\@currbox \fi
      \@tempdima\@mparbottom
      \advance\@tempdima -\@pageht
      \advance\@tempdima\ht\@marbox
      \ifdim\@tempdima >\z@
         \@latex@warning@no@line {Marginpar on page \thepage\space moved}%
      \else
         \@tempdima\z@
      \fi
      \global\@mparbottom\@pageht
      \global\advance\@mparbottom\@tempdima
      \global\advance\@mparbottom\dp\@marbox
      \global\advance\@mparbottom\marginparpush
      \advance\@tempdima -\ht\@marbox
      \global\setbox \@marbox
      \vbox {\vskip \@tempdima
         \box \@marbox}%
      \global \ht\@marbox \z@
      \global \dp\@marbox \z@
      \kern -\@pagedp
      \nointerlineskip
      \hb@xt@\columnwidth
      {\ifnum \@tempcnta >\z@
            %          \hskip\columnwidth \hskip20pt\hskip\marginparsep
            \hskip\typewidth\hskip6pt
         \else
            \hskip -\marginparsep \hskip -\marginparwidth
            \hskip-\colmargin\hskip-\texttypewidthsep\hskip-6pt
         \fi
         \box\@marbox \hss}%
      \nointerlineskip
      \hbox{\vrule \@height\z@ \@width\z@ \@depth\@pagedp}}
   %

   \def\firstpage#1{#1}
   \def\lastpage#1{#1}

   \def\doitext{doi:}
   \def\voltext{\ifcopoddhead{Vol.}\else{vol.}\fi}
\def\isstext{No.}
\def\journal#1{\gdef\journalname{#1}}
\def\edtext{e}
\def\jid#1{\gdef\jidval{#1}}
\def\jnlDoiYr#1{\gdef\@jnlDoiYr{#1}}\jnlDoiYr{}%
\def\jnlPage#1#2{\gdef\first@page{\thepage}\gdef\last@page{#2}}


\def\doilink#1{\ifonline\href{https://doi.org/#1}{\textcolor{blue}{#1}}\else#1\fi}
\def\volno#1{\gdef\@volno{#1}}\volno{}%
\def\issno#1{\gdef\@issueno{#1}}\issno{}%
\def\doival#1{\gdef\@doi{\doilink{#1}}}\doival{}%
\def\thehead#1{\gdef\@thehead{#1}}\thehead{}%
\def\edno#1{\gdef\@edno{#1}}\edno{}%


%\def\aff#1{{$^{#1}$}}


\def\journaltitle#1{\gdef\@journaltitle{#1}}\journaltitle{Mathematical Structures in Computer}%
\def\cpr#1{\gdef\@cpr{#1}}

\def\OAlink{http://creativecommons.org/licenses/by/4.0/}

\def\OAtext#1{\gdef\@OAtext{#1}}

\OAtext{This is an Open Access article, distributed under the terms of the Creative Commons Attribution licence\newline \hbox{(\iffinals\OAlink\else\href{\OAlink}{\OAlink}\fi),} which permits unrestricted re-use, distribution, and reproduction in any medium, provided the
   original work is properly cited.}

\cpr{\ifOA \vbox{\copyright\ Cambridge University Press\ \@jnlDoiYr. \@OAtext}\else \copyright\ Cambridge University Press\ \@jnlDoiYr\fi}%


\def\corresp#1{\affilfont\@par#1}

\def\aopfoot#1{\gdef\@aopfoot{#1}}\aopfoot{}

\let\save@clearpage\clearpage
\let\save@outputpage\@outputpage

\def\store@outputpage{%
   \global\setbox\store@outputbox \vbox to \storedboxheight{%
      \leftline{\box\@outputbox}\vss}%
   \noindent%\fbox
   {\box\store@outputbox}%
   \par%\vrule width\textwidth height1pt
   \global\let\@outputpage\save@outputpage}
%
\def\balancepage{\@ifnextchar[{\balancecolpagebreak}{\balancecolpagebreak[0pt]}}
\def\balancecolpagebreak[#1]{\ifvmode\vadjust\fi{\vskip-\baselineskip%\vskip-12pt
\leftline{\vrule width\typewidth height\draftrule depth0pt}%
\expandafter\ifdim#1=0pt\vfill\else\vskip#1\fi}\pagebreak}
%
\def\balanceandcontinue{%
   \par
   \ifdim\pagegoal=\maxdimen
   \else
      \global\let\@outputpage\store@outputpage
      \ifdim\@colht=\pagegoal
         \global\storedboxheight\pagetotal
      \else
         \global\storedboxheight\@colht
         \global\advance\storedboxheight-\pagegoal
         \global\advance\storedboxheight\pagetotal
         %         \global\advance\storedboxheight12pt
      \fi
   \fi
   \onecolumn
   \global\switchcolstrue}
%
\def\TwoColumn{\@ifnextchar[{\@TwoColumn}{\@TwoColumn[]}}
\def\@TwoColumn[#1]{%
   \balanceandcontinue
   \let\clearpage\relax
   \def\@tempa{#1}%
   \ifx\@tempa\@empty
      \twocolumn
   \else
      #1\global\@partialpageht\pagetotal\twocolumn
   \fi
   \let\clearpage\save@clearpage}
%
\def\OOnecolumn{%
   %  \clearpage
   \global\columnwidth\textwidth
   \global\hsize\columnwidth
   \global\linewidth\columnwidth
   \global\@twocolumnfalse
   \col@number \@ne
   \@floatplacement}
%
\def\twotoonecol#1{\TwoColumn[#1]}
%

\def\keyhead{}
%
\newenvironment{keywords}{%
   \global\setbox\keywordbox%
   \vbox\bgroup%
   \noindent{\keyheadfont\keywordname :} \keywordfont%
   \parindent0pt}
{\egroup}
%
\def\abstractsource#1{%
   \vskip3pt\rightline{\upshape#1}}
%
\def\introhead#1{\section*{#1}}%
%
\def\subchapter#1{\gdef\@subchapter{#1}}
\subchapter{}%
%
%%%%%%%%%%%%%%%%%%%% Author %%%%%%%%%%%%%%%%%%%%
%
\gdef\hrec{received}
\gdef\hrev{rev-recd}
\gdef\hacc{accepted}
\gdef\hpub{epubdate}
\gdef\hdcv{currentversion}
%\gdef\AFF{aff}%
\gdef\RECEIVED{received}%

\def\receivedtext{Received\ }
\def\revisedtext{revised\ }
\def\acceptedtext{accepted\ }
\def\publishedtext{published\ }
\def\cvtext{current version\ }

\def\Jan{January}
\def\Feb{February}
\def\Mar{March}
\def\Apr{April}
\def\May{May}
\def\June{June}
\def\July{July}
\def\Aug{August}
\def\Sep{September}
\def\Oct{October}
\def\Nov{November}
\def\Dec{December}

\def\monthi{01}
\def\monthii{02}
\def\monthiii{03}
\def\monthiv{04}
\def\monthv{05}
\def\monthvi{06}
\def\monthvii{07}
\def\monthviii{08}
\def\monthix{09}
\def\monthx{10}
\def\monthxi{11}
\def\monthxii{12}

\def\monthvalue{%
   \ifx\monthnum\monthi%
      \Jan%
   \else%
      \ifx\monthnum\monthii%
         \Feb%
      \else%
         \ifx\monthnum\monthiii%
            \Mar%
         \else%
            \ifx\monthnum\monthiv%
               \Apr%
            \else%
               \ifx\monthnum\monthv%
                  \May%
               \else%
                  \ifx\monthnum\monthvi%
                     \June%
                  \else%
                     \ifx\monthnum\monthvii%
                        \July%
                     \else%
                        \ifx\monthnum\monthviii%
                           \Aug%
                        \else%
                           \ifx\monthnum\monthix%
                              \Sep%
                           \else%
                              \ifx\monthnum\monthx%
                                 \Oct%
                              \else%
                                 \ifx\monthnum\monthxi%
                                    \Nov%
                                 \else%
                                    \ifx\monthnum\monthxii%
                                       \Dec%
                                    \else%
                                    \fi\fi\fi\fi\fi\fi\fi\fi\fi\fi\fi\fi}

\def\affcomma{\global\@affseptrue}
%
\def\auand{\unskip\unskip\unskip\comma\nobreakspace{}\unskip\unskip\unskip}%
\def\aurunand{\unskip\unskip\unskip\comma}%
\def\aulastand{\ and}%
\def\auandname{\ and\ }%

\renewcommand{\author}[2][]{%
   \gdef\au@data{yes}%
   \expandafter\protected@xdef\csname author\the\authorcount\endcsname{#2{\ifonline\protect\hyperlink{au#1}{\textrm{#1}}\else#1\fi}}%
   \global\advance\authorcount1}

\gdef\@author{%
   \global\tempauthorcount\authorcount%
   \global\advance\tempauthorcount-1%
   \global\authorcommacount\tempauthorcount%
   \global\advance\authorcommacount-1%
   \global\authortempcount0%
   \global\authortempcount0%
   \ifnum\authorcount=1%
      \ignorespaces\csname author0\endcsname%
   \else%
      \ifnum\authorcount=2%
         \ignorespaces\csname author0\endcsname \auandname \csname author1\endcsname%
      \else%
         \@whilenum\tempcount<\tempauthorcount%
         \do{%\vskip8pt
            \csname author\the\tempcount\endcsname\ %
            \global\advance\tempcount1}%
         \aulastand \csname author\the\tempcount\endcsname\unskip%
      \fi%
   \fi}

\def\printauthor{\if@editorial\else\@author\fi}



\gdef\keyword@data{no}%

\def\keyword#1{\unskip%
   \gdef\keyword@data{yes}%
   \expandafter\protected@xdef\csname keyword\the\keywordcount\endcsname{#1}%
   \global\advance\keywordcount1%
}%

\def\printkeyword{\keyfont{\keyheadfont{\keyhead}}%
   \global\tempkeywordcount\keywordcount%
   \global\keytempcount0%
   \global\advance\tempkeywordcount-1
   \@whilenum\keytempcount<\tempkeywordcount%
   \do{\csname keyword\the\keytempcount\endcsname\comma\ %
      \global\advance\keytempcount1}%
   \csname keyword\the\keytempcount\endcsname\fullstop\@@par}%

\def\diffaffnum#1{\expandafter\@diffaffnum\csname c@#1\endcsname}

\def\@diffaffnum#1{%
   \ifcase#1\or a\or b\or c\or d\or e\or f\or g\or h\or i\or j\or
      k\or l\or m\or n\or o\or p\or q\or r\or s\or t\or u\or v\or w\or x\or
      y\or z\else\@ctrerr\fi}

\def\theaffidalph{\diffaffnum{affidalph}}

\def\push@affidconcord#1{\add@affidname#1}%

\gdef\add@affidname{\expandafter\affidname}%

\gdef\affidname#1#2{#2}%

\def\memid{}

\def\noaffnum{\global\@oneoffnumtrue}

\def\affiliation#1{%
   \expandafter\protected@xdef\csname affil\the\affilcount\endcsname{#1}%
   \global\advance\affilcount1}%

\def\printaffil{%
   \global\tempaffilcount\affilcount%
   \global\affiltempcount0%
   \global\advance\tempaffilcount-1
   \ifnum\affilcount=1%
      \ignorespaces\csname affil0\endcsname%
      \protected@write\@auxout{}{\string\noaffnum}%
   \else%
      \@whilenum\affiltempcount<\tempaffilcount%
      \do{\csname affil\the\affiltempcount\endcsname\@@par%
         \global\advance\affiltempcount1}%
      \csname affil\the\affiltempcount\endcsname\@@par\fi}%

\gdef\member#1{%
   \expandafter\protected@xdef\csname member\the\membercount\endcsname{#1}%
   \global\advance\membercount1}%

\def\printmember{%
   \global\tempmembercount\membercount%
   \global\membertempcount0%
   \global\advance\tempmembercount-1
   \@whilenum\membertempcount<\tempmembercount%
   \do{\csname member\the\membertempcount\endcsname\@@par%
      \global\advance\membertempcount1}%
   \csname member\the\membertempcount\endcsname\@@par}%
\def\editorbreak{\end{tabular}\vfill\pagebreak  \begin{tabular}{@{}l@{}}\\[-36pt]}
\def\editorsbiography{\par\leftskip-22pc}

\def\history#1{%
   \expandafter\protected@xdef\csname history\the\historycount\endcsname{#1}%
   \global\advance\historycount1}%

\def\printhistory{\historyfont%
   \global\temphistorycount\historycount%
   \global\historytempcount0%
   \global\advance\temphistorycount-1%
   \@whilenum\historytempcount<\temphistorycount%
   \do{\csname history\the\historytempcount\endcsname%
      \global\advance\historytempcount1}%
   \csname history\the\historytempcount\endcsname\unskip}%

\def\tthanks#1{\gdef\@tthanks{\affilfont#1}}\tthanks{}

\sodef\ptso{}{1pt}{0pt}{0pt}

\def\papertitle#1{\gdef\@articletitt{\ptso{\MakeUppercase{#1}}}}\papertitle{}%

\def\citeauth#1{\gdef\@citeauth{#1}}\citeauth{}

\def\maketitle{\par%
   \begingroup%
   %\parindent0pt%
   %    \renewcommand\thefootnote{\@fnsymbol\c@footnote}%
   %  \def\@makefnmark{\rlap{\@textsuperscript{\scriptsize\@thefnmark}}}%
   %   \long\def\@makefntext##1{##1}%
   \@maketitle%
   \endgroup
   %  \renewcommand\thefootnote{}%
   \ifx\@aopfoot\@empty%
   \else%
      \footnotetext{{\corresfont{\@aopfoot}}}
      \setcounter{footnote}{0}%
   \fi%
   \advance\keywordcount0%
   \advance\authorcount0
   \enlargethispage{-12pt}}

\newif\ifneedspace\global\needspacefalse%

\newenvironment{abshade}{\topsep0pt%
   \def\FrameCommand{\fboxsep=0pt \colorbox{absshadecolor}}%
   \MakeFramed {\FrameRestore}}%
{\endMakeFramed}

\def\absheadfont{\fontsize{9}{10}\fontfamily{\sfdefault}\fontseries{sb}\fontshape{n}\selectfont}

\newbox\maketitlebox

\def\@maketitle{\par\rightskip0pt plus1fill%
   \ifx\@subtitle\@empty%
   \else%
      \vskip-10.5pt%
      {\subtitlefont\@subtitle\vphantom{y}\vskip10.5pt}%
   \fi%
   \vspace*{-5.1pt}
   \parindent0pt%
   {\artitfont\@articletitt\vphantom{y}\vskip15pt}
   {\titlefont\@title\vphantom{y}\vskip12.3pt}%
   {\authorfont{\printauthor\vphantom{y}}\vskip7pt}%
   {\affilfont\printaffil\vskip6.5pt}
   {\printhistory}\vskip9pt%
   \begin{abshade}\vskip9pt%
      \noindent \hspace*{9pt}{\absheadfont\abstractname}\vskip4.5pt%
      {\unvbox\abstractbox}%
      \vskip7pt\end{abshade}\vskip12pt%
   {\unvbox\keywordbox}\vskip32pt%
   \@afterheading%
   \@afterindentfalse%
   \setcounter{section}{0}}

\headlineindent=2.5cc

%%%%%%%%%%%%%%%%%%%% Affiliation %%%%%%%%%%%%%%%%%%%%
%
\def\subtitle#1{\gdef\@subtitle{#1}}\subtitle{}
%
%%%%%%%%%%%%%%%%%%%%% Copyright %%%%%%%%%%%%%%%%%%%%
%
\def\Copyright#1{\gdef\@Copyright{#1}}
\Copyright{}%
%
%%%%%%%%%%%%%%%%%%%% Chapter Head %%%%%%%%%%%%%%%%%%%%
%
\def\dummycharacter{\vphantom{ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz}}
%
\def\chapfig#1{\gdef\@chapfig{\epsfbox{\ArtDir #1}}}\chapfig{Chap-01.eps}
%
\def\ai#1{\gdef\@ai{$^{\text{#1}}$}}\ai{}
\def\aii#1{\gdef\@aii{$^{\text{#1}}$}}\aii{}
\def\aiii#1{\gdef\@aiii{$^{\text{#1}}$}}\aiii{}
\def\aiv#1{\gdef\@aiv{$^{\text{#1}}$}}\aiv{}
\def\av#1{\gdef\@av{$^{\text{#1}}$}}\av{}
\def\avi#1{\gdef\@avi{$^{\text{#1}}$}}\avi{}
\def\avii#1{\gdef\@avii{$^{\text{#1}}$}}\avii{}
\def\aviii#1{\gdef\@aviii{$^{\text{#1}}$}}\aviii{}
\def\aix#1{\gdef\@aix{$^{\text{#1}}$}}\aix{}
\def\ax#1{\gdef\@ax{$^{\text{#1}}$}}\ax{}
%
\newcommand\theaffilnote{\arabic{afrfilnote}}
%
\setcounter{secnumdepth}{4}
\renewcommand\thepart          {\Roman{part}}
\renewcommand\thechapter       {\arabic{chapter}}
\renewcommand\thesection       {\ifappendix \Alph{section}\else\arabic{section}\fi}
\renewcommand\thesubsection    {\thesection.\arabic{subsection}}
\renewcommand\thesubsubsection {\thesubsection.\arabic{subsubsection}}
\renewcommand\theparagraph     {\thesubsubsection.\arabic{paragraph}}
\renewcommand\thesubparagraph  {\arabic{subparagraph}}
%
\renewcommand\theHLsection{\ifnum\c@secnumdepth=0\else\theHLtitle.\arabic{HLsection}\fi}%%%%
\renewcommand\theHLsubsection{\ifnum\c@secnumdepth=0\else\theHLsection.\arabic{HLsubsection}\fi}%%%%
\renewcommand\theHLsubsubsection{\ifnum\c@secnumdepth=0\else\theHLsubsection.\arabic{HLsubsubsection}\fi}%%%%
%
\def\subsubsectionsymfont{\fontfamily{\zpdefault}\fontsize{10}{12}\selectfont}
\def\subsubsectionsym{\ignorespaces\hspace*{4pt}{\subsubsectionsymfont\mycolor{\colorfive n}}}
%
\def\reviewsymfont{\fontfamily{\zpdefault}\fontsize{12}{12}\selectfont}
\def\reviewsym{\mycolor{\colorseven\raise.65pt\hbox to 0pt{\vrule height7pt width1pt\hspace*{.5pt}\vrule height7pt width2pt\hspace*{.5pt}\vrule height7pt width3pt\hspace*{.5pt}\vrule height7pt width6pt}\hspace*{12pt}\reviewsymfont\char'347\hspace*{12pt}}}
\def\probhrulefill{\mycolor{\colorseven\leavevmode\leaders\hrule height1pt\hfill\kern\z@}}
%
\def\acknoheadfont{\sectionfont}
%
\newcommand\section{\@startsection {section}{1}{\z@}{26pt plus1pt minus1pt}{3pt}{\sectionfont}}%
\newcommand\subsection{\@startsection{subsection}{2}{\z@}{25pt plus1pt minus1pt}{2pt}{\subsectionfont}}%
\newcommand\subsubsection{\@startsection{subsubsection}{3}{\z@}{22pt plus1pt minus1pt}{.1pt}{\subsubsectionfont}}%
\newcommand\paragraph{\@startsection{paragraph}{4}{\z@}{6pt}{-1.5pt}{\paragraphfont}}%
\newcommand\subparagraph{\@startsection{subparagraph}{5}{\parindent}{-19pt \@plus -2pt \@minus -.2pt}{-1em}{\subparagraphfont}}%
\newcommand\subsubparagraph{\@startsection{subsubparagraph}{6}{\parindent}{-19pt \@plus -2pt \@minus -.2pt}{-1em}{\subsubparagraphfont}}%
%
\newcommand\referencehead{\@startsection {section}{1}{\z@}{-24pt \@plus -2pt \@minus -.2pt}{2pt}{\referenceheadfont}}%
\newcommand\acknohead{\@startsection {section}{1}{\z@}{-24pt \@plus -2pt \@minus -.2pt}{6pt}{\acknoheadfont}}%

\def\@seccntformat#1{\csname the#1\endcsname}

\def\@sect#1#2#3#4#5#6[#7]#8{\Abstractfalse%
   \ifnum #2>\c@secnumdepth
      \let\@svsec\@empty
   \else
      \refstepcounter{#1}%
      \protected@edef\@svsec{\@seccntformat{#1}\ifnum#2=1.\hspace*{5.5pt}\else\hspace*{3pt}\fi\relax}%
   \fi
   \@tempskipa #5\relax
   \ifdim \@tempskipa>\z@
      \begingroup
      #6{%
         \ifnum#2=1%
            %\def\spreadoutfactor{-.6}%
            \@hangfrom{\hskip #3\relax\ifappendix Appendix \@svsec\else\@svsec\fi}%
            \interlinepenalty \@M #8\@@par%
         \else%
            \ifnum#2=2%
               \@hangfrom{\hskip #3\relax\@svsec}%
               \interlinepenalty \@M #8\@@par%
            \else
               \ifnum#2=3%
                  \@hangfrom{\hskip #3\relax\@svsec}%
                  \interlinepenalty \@M #8\@@par%
               \else%
                  %\ifnum#2=4%
                  \@hangfrom{\hskip #3\relax\@svsec}%
                  \interlinepenalty \@M #8\@@par%
               \fi\fi\fi}%
      \endgroup
      \csname #1mark\endcsname{#7}%
      \addcontentsline{toc}{#1}{%
         \ifnum #2>\c@secnumdepth \else
            \protect\numberline{\csname the#1\endcsname}%
         \fi
         #7}%
   \else
      \def\@svsechd{%
         #6{\hskip #3\relax
               \@svsec #8\ifnum#2=4%
                  \hspace*{2pt}\else\fi}%
         \csname #1mark\endcsname{#7}%
         \addcontentsline{toc}{#1}{%
            \ifnum #2>\c@secnumdepth \else
               \protect\numberline{\csname the#1\endcsname}%
            \fi
            #7}}%
   \fi
   \@xsect{#5}}
%
\def\@ssect#1#2#3#4#5{%
   \@tempskipa #3\relax
   \ifdim \@tempskipa>\z@
      \ifreview%
         \begingroup
         #4{%
            \@hangfrom{\hskip #1}%
            \interlinepenalty \@M {\reviewsym}{{#5}}\@@par}%
         \endgroup
      \else%
         \begingroup
         #4{%
            \@hangfrom{\hskip #1}%
            \interlinepenalty \@M {#5}\@@par}%
         \endgroup
      \fi%
   \else
      \def\@svsechd{#4{\hskip #1\relax #5\enspace}}%
   \fi
   \@xsect{#3}}
%
\def\@startsection#1#2#3#4#5#6{%
   \if@noskipsec \leavevmode \fi
   \par
   \@tempskipa #4\relax
   \@afterindentfalse
   \ifdim \@tempskipa <\z@
      \@tempskipa -\@tempskipa
   \fi
   \if@nobreak
      \everypar{}%
   \else
      \addpenalty\@secpenalty\addvspace\@tempskipa
   \fi
   \@ifstar
   {\@ssect{#3}{#4}{#5}{#6}}%
   {\@dblarg{\@sect{#1}{#2}{#3}{#4}{#5}{#6}}}}
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  End Sectioning commands  %%%%%%%%%%%%%%%%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  Lists %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
\topsepi12\p@ \@plus2\p@% \@minus.5\p@
\topsepii2pt% \@plus1\p@
\topsepiii2pt% \@plus1\p@
\topsepiv2pt% \@plus1\p@
\topsepv2pt% \@plus1\p@
\topsepvi2pt% \@plus1\p@
\topsepvii2pt% \@plus1\p@
\topsepviii2pt% \@plus1\p@
\topsepix2pt% \@plus1\p@
\topsepx2pt% \@plus1\p@
\itemsepi0pt
\itemsepii0pt
\itemsepiii0pt
\itemsepiv0pt
\itemsepv0pt
\itemsepvi0pt
\itemsepvii0pt
\itemsepviii0pt
\itemsepix0pt
\itemsepx0pt
%
\def\list#1#2{%
   \ifnum \@listdepth >10\relax
      \@toodeep
   \else
      \global\advance\@listdepth\@ne
   \fi
   \rightmargin\z@
   \listparindent\z@
   \itemindent\z@
   \csname @list\romannumeral\the\@listdepth\endcsname
   \def\@itemlabel{#1}%
   \let\makelabel\@mklab
   \@nmbrlistfalse
   #2\relax
   \@trivlist
   \parskip\parsep
   \parindent\listparindent
   \advance\linewidth -\rightmargin
   \advance\linewidth -\leftmargin
   \advance\@totalleftmargin \leftmargin
   \parshape \@ne \@totalleftmargin \linewidth
   \ignorespaces}
%
\def\@listI{\leftmargin\leftmargini
   \labelwidth\leftmargini
   \advance\labelwidth-\labelsep
   \parsep 0\p@%
   \topsep \topsepi
   \itemsep\itemsepi}%
\let\@listi\@listI
\@listi
\def\@listii {\leftmargin\leftmarginii
   \labelwidth\leftmarginii
   \advance\labelwidth-\labelsep
   \topsep\topsepii
   \parsep 0pt
   \itemsep\itemsepii}
\def\@listiii {\leftmargin\leftmarginiii
   \labelwidth\leftmarginiii
   \advance\labelwidth-\labelsep
   \topsep\topsepiii
   \parsep 0pt
   \itemsep\itemsepiii}
\def\@listiv {\leftmargin\leftmarginiv
   \labelwidth\leftmarginiv
   \advance\labelwidth-\labelsep}
\def\@listv  {\leftmargin\leftmarginv
   \labelwidth\leftmarginv
   \advance\labelwidth-\labelsep}
\def\@listvi {\leftmargin\leftmarginvi
   \labelwidth\leftmarginvi
   \advance\labelwidth-\labelsep}
\def\@listvii {\leftmargin\leftmarginvii
   \labelwidth\leftmarginvii
   \advance\labelwidth-\labelsep}
\def\@listviii {\leftmargin\leftmarginviii
   \labelwidth\leftmarginviii
   \advance\labelwidth-\labelsep}
\def\@listix {\leftmargin\leftmarginix
   \labelwidth\leftmarginix
   \advance\labelwidth-\labelsep}
\def\@listx {\leftmargin\leftmarginx
   \labelwidth\leftmarginx
   \advance\labelwidth-\labelsep}
%
\setlength\leftmargini  {2.5em}
\setlength\leftmarginii  {2.2em}
\setlength\leftmarginiii {1.87em}
\setlength\leftmarginiv  {1.7em}
\setlength\leftmarginv  {1em}
\setlength\leftmarginvi {1em}
\setlength\leftmarginvii {1em}
\setlength\leftmarginviii {1em}
\setlength\leftmarginix {1em}
\setlength\leftmarginx {1em}
\setlength\leftmargin    {\leftmargini}
%
\setlength  \labelsep  {\LabelSep}
\setlength  \labelwidth{\leftmargini}
\addtolength\labelwidth{-\labelsep}
%
\newcommand\theenumv{\Alph{enumv}}
\newcommand\theenumvi{\Alph{enumvi}}
\newcommand\theenumvii{\roman{enumvii}}
\newcommand\theenumviii{\Alph{enumviii}}
\newcommand\theenumix{\Alph{enumix}}
\newcommand\theenumx{\roman{enumx}}
\renewcommand\theenumi{\arabic{enumi}}
\renewcommand\theenumii{\alph{enumii}}
\renewcommand\theenumiii{\roman{enumiii}}
\renewcommand\theenumiv{\Alph{enumiv}}
\renewcommand\theenumv{\Alph{enumv}}
\renewcommand\theenumvi{\Alph{enumvi}}
\renewcommand\theenumvii{\Alph{enumvii}}
\renewcommand\theenumviii{\Alph{enumviii}}
\renewcommand\theenumix{\Alph{enumix}}
\renewcommand\theenumx{\Alph{enumx}}
\newcommand\labelenumi{(\theenumi)}
\newcommand\labelenumii{\theenumii.}
\newcommand\labelenumiii{\theenumiii.}
\newcommand\labelenumiv{\theenumiv.}
\newcommand\labelenumv{\theenumv.}
\newcommand\labelenumvi{\theenumvi.}
\newcommand\labelenumvii{\theenumvii.}
\newcommand\labelenumviii{\theenumviii.}
\newcommand\labelenumix{\theenumix.}
\newcommand\labelenumx{\theenumx.}
\renewcommand\p@enumii{\theenumi}
\renewcommand\p@enumiii{\theenumi(\theenumii)}
\renewcommand\p@enumiv{\p@enumiii\theenumiii}
\font\lcir = lcircle10 at 12pt
\newcommand\bulls{\raise1.5pt\hbox{\lcir\char'162}}
\def\textbullet{\leavevmode\raise2pt\hbox{\hskip2pt\bulls}}
\def\textendash{{\bf--}}
\def\textasteriskcentered{\leavevmode\raise-1.5pt\hbox{*}}
\def\textperiodcentered{\leavevmode\raise1.5pt\hbox{\bulls}}
\newcommand\labelitemi{\textbullet}
\newcommand\labelitemii{\normalfont\bfseries \textendash}
\newcommand\labelitemiii{\textasteriskcentered}
\newcommand\labelitemiv{\textperiodcentered}
\newcommand\labelitemv{\textperiodcentered}
\newcommand\labelitemvi{\textbullet}
\newcommand\labelitemvii{\normalfont\bfseries \textendash}
\newcommand\labelitemviii{\textasteriskcentered}
\newcommand\labelitemix{\textperiodcentered}
\newcommand\labelitemx{\textperiodcentered}
%
\newenvironment{verse}
{\let\\=\@centercr
   \list{}{\itemsep      \z@
      \itemindent   -1.5em%
      \listparindent\itemindent
      \rightmargin  \leftmargin
      \advance\leftmargin 1.5em}%
   \item[]}
{\endlist}
%
\newenvironment{extract}
{\let\\=\@centercr
   \list{}{\itemsep      \z@
      \leftmargin10pt%
      \rightmargin\leftmargin}%
   \item[]}
{\endlist}


\newenvironment{OL}{\par\addvspace{9pt plus2pt}%

   \def\listdevicefonti{\bf}
   \def\listdevicefontii{\bf}
   \def\listdevicefontiii{\bf}
   \def\listdevicefontiv{\bf}
   \def\listdevicefontv{\bf}
   \def\listdevicefontvi{\bf}
   \def\listdevicefontvii{\bf}
   \def\listdevicefontviii{\bf}
   \def\listdevicefontix{\bf}
   \def\listdevicefontx{\bf}
   \let\eqnarray\oleqnarray
   %\let\[\eq

   \mathindent\itemleftmargin
   \renewcommand\labelenumv{(\theenumv)}
   \renewcommand\labelenumvi{(\theenumvi)}
   \renewcommand\labelenumvii{(\theenumvii)}
   \labelsepi3.8pt
   \labelsepii3.8pt
   \labelsepiii3.8pt
   \labelsepiv3.8pt
   \labelsepv3.8pt
   \labelsepvi3.8pt
   \labelsepvii3.8pt
   \abovelistskipi0pt%
   \belowlistskipi0pt%
   \abovelistskipii0pt%
   \belowlistskipii0pt%
   \abovelistskipiii0pt%
   \belowlistskipiii0pt%
   \abovelistskipiv0pt%
   \belowlistskipiv0pt%
   \abovelistskipv0pt%
   \belowlistskipv0pt%
   \abovelistskipvi0pt%
   \belowlistskipvi0pt%
   \abovelistskipvii0pt%
   \belowlistskipvii0pt%
   \abovelistskipviii0pt%
   \belowlistskipviii0pt%
   \abovelistskipix0pt%
   \belowlistskipix0pt%
   \abovelistskipx0pt%
   \belowlistskipx0pt%
}{
   \par\addvspace{9pt plus2pt}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  End Lists %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  Enumerate list %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
\listtextleftmargin 0pt%24pt
\listtextleftmarginii0pt% 24pt
\listtextleftmarginiii0pt% 24pt
\listtextleftmarginiv0pt% 24pt
\listtextleftmarginv0pt% 24pt
\listtextleftmarginvi0pt% 24pt
\listtextleftmarginvii0pt% 24pt
\listtextleftmarginviii0pt% 24pt
\listtextleftmarginix0pt% 24pt
\listtextleftmarginx0pt% 24pt
\listtextrightmargin0pt%.5pc
\listlabelleftskip0pt%3.3pt
\listlabelleftskipii0pt%3.3pt
\listlabelleftskipiii0pt%3.3pt
\listlabelleftskipiv0pt%3.3pt
\listlabelleftskipv0pt%3.3pt
\listlabelleftskipvi0pt%3.3pt
\listlabelleftskipvii0pt%3.3pt
\listlabelleftskipviii0pt%3.3pt
\listlabelleftskipix0pt%3.3pt
\listlabelleftskipx0pt%3.3pt
\abovelistskipi12pt%
\belowlistskipi12pt%
\abovelistskipii0pt% plus2pt
\belowlistskipii0pt% plus2pt
\abovelistskipiii0pt% plus2pt
\belowlistskipiii0pt% plus2pt
\abovelistskipiv0pt% plus2pt
\belowlistskipiv0pt% plus2pt
\abovelistskipv0pt% plus2pt
\belowlistskipv0pt% plus2pt
\abovelistskipvi0pt% plus2pt
\belowlistskipvi0pt% plus2pt
\abovelistskipvii0pt% plus2pt
\belowlistskipvii0pt% plus2pt
\abovelistskipviii0pt% plus2pt
\belowlistskipviii0pt% plus2pt
\abovelistskipix0pt% plus2pt
\belowlistskipix0pt% plus2pt
\abovelistskipx0pt% plus2pt
\belowlistskipx0pt% plus2pt
\labelsepi5.4pt
\labelsepii5.2pt
\labelsepiii\z@
\labelsepiv\z@
\labelsepv\z@
\labelsepvi\z@
\labelsepvii\z@
\labelsepviii\z@
\labelsepix\z@
\labelsepx\z@
%
\def\listdevicefonti{}
\def\listdevicefontii{}
\def\listdevicefontiii{}
\def\listdevicefontiv{}
\def\listdevicefontv{}
\def\listdevicefontvi{}
\def\listdevicefontvii{}
\def\listdevicefontviii{}
\def\listdevicefontix{}
\def\listdevicefontx{}
\def\listfont{}
\def\textlistlabel{}
%
\@definecounter{enumv}
\@definecounter{enumvi}
\@definecounter{enumvii}
\@definecounter{enumviii}
\@definecounter{enumix}
\@definecounter{enumx}
%
\def\enummax#1{%
   \labelsep\csname labelsep\romannumeral\the\@enumdepth\endcsname
   \ifdim\listtextleftmargin>\z@\labelsepi0pt\fi
   \ifdim\listtextleftmarginii>\z@\labelsepii0pt\fi
   \ifdim\listtextleftmarginiii>\z@\labelsepiii0pt\fi
   \setbox\tempbox\hbox{\csname listdevicefont\romannumeral\the\@enumdepth\endcsname#1\hskip\labelsep}%
   \enumdim\wd\tempbox
   \setbox\tempbox\hbox{\csname listdevicefont\romannumeral\the\@enumdepth\endcsname#1}%
   \enumdimwd\wd\tempbox
   \expandafter\global\csname leftmargin\romannumeral\the\@enumdepth\endcsname\enumdim
   \ifdim\listtextleftmargin>\z@
      \leftmargini\listtextleftmargin
      \ifdim\listlabelleftskip>\z@
         \advance\leftmargini-\listlabelleftskip
      \fi
   \fi
   \ifdim\listtextleftmarginii>\z@
      \leftmarginii\listtextleftmarginii
      \ifdim\listlabelleftskipii>\z@
         \advance\leftmarginii-\listlabelleftskipii
      \fi
   \fi
   \ifdim\listtextleftmarginiii>\z@
      \leftmarginiii\listtextleftmarginiii
      \ifdim\listlabelleftskipiii>\z@
         \advance\leftmarginiii-\listlabelleftskipiii
      \fi
   \fi
   \ifdim\listtextleftmarginiv>\z@
      \leftmarginiv\listtextleftmarginiv
      \ifdim\listlabelleftskipiv>\z@
         \advance\leftmarginiv-\listlabelleftskipiv
      \fi
   \fi
   \ifdim\listtextleftmarginv>\z@
      \leftmarginv\listtextleftmarginv
      \ifdim\listlabelleftskipv>\z@
         \advance\leftmarginv-\listlabelleftskipv
      \fi
   \fi
   \ifdim\listtextleftmarginvi>\z@
      \leftmarginvi\listtextleftmarginvi
      \ifdim\listlabelleftskipvi>\z@
         \advance\leftmarginvi-\listlabelleftskipvi
      \fi
   \fi
   \ifdim\listtextleftmarginvii>\z@
      \leftmarginvii\listtextleftmarginvii
      \ifdim\listlabelleftskipvii>\z@
         \advance\leftmarginvii-\listlabelleftskipvii
      \fi
   \fi
   \ifdim\listtextleftmarginviii>\z@
      \leftmarginviii\listtextleftmarginviii
      \ifdim\listlabelleftskipviii>\z@
         \advance\leftmarginviii-\listlabelleftskipviii
      \fi
   \fi
   \ifdim\listtextleftmarginix>\z@
      \leftmarginix\listtextleftmarginix
      \ifdim\listlabelleftskipix>\z@
         \advance\leftmarginix-\listlabelleftskipix
      \fi
   \fi
   \ifdim\listtextleftmarginx>\z@
      \leftmarginx\listtextleftmarginx
      \ifdim\listlabelleftskipx>\z@
         \advance\leftmarginx-\listlabelleftskipx
      \fi
   \fi
   \ifdim\listlabelleftskip>\z@
      \advance\leftmargini\listlabelleftskip
   \fi
   \ifdim\listlabelleftskipii>\z@
      \advance\leftmarginii\listlabelleftskipii
   \fi
   \ifdim\listlabelleftskipiii>\z@
      \advance\leftmarginiii\listlabelleftskipiii
   \fi
   \ifdim\listlabelleftskipiv>\z@
      \advance\leftmarginiv\listlabelleftskipiv
   \fi
   \ifdim\listlabelleftskipv>\z@
      \advance\leftmarginv\listlabelleftskipv
   \fi
   \ifdim\listlabelleftskipvi>\z@
      \advance\leftmarginvi\listlabelleftskipvi
   \fi
   \ifdim\listlabelleftskipvii>\z@
      \advance\leftmarginvii\listlabelleftskipvii
   \fi
   \ifdim\listlabelleftskipviii>\z@
      \advance\leftmarginviii\listlabelleftskipviii
   \fi
   \ifdim\listlabelleftskipix>\z@
      \advance\leftmarginix\listlabelleftskipix
   \fi
   \ifdim\listlabelleftskipx>\z@
      \advance\leftmarginx\listlabelleftskipx
   \fi
}
%
\enummax{1.}
%
\def\enumerate{\@ifnextchar[{\@enumerate}{\@enumerate[\csname label\@enumctr\endcsname]}}%%
%
\def\@enumerate[#1]{\par
   \ifnum \@enumdepth >10 \@toodeep
   \else
      \advance\@enumdepth\@ne
      \edef\@enumctr{enum\romannumeral\the\@enumdepth}%
      \setcounter{\@enumctr}{1}\enummax{#1}%
      \list
      {\csname label\@enumctr\endcsname}{\usecounter{\@enumctr}%
         \topsep\csname abovelistskip\romannumeral\the\@enumdepth\endcsname
         \itemsep\csname itemsep\romannumeral\the\@enumdepth\endcsname
         \listfont %\listparindent18.25pt
         \ifnum \@enumdepth=1
            \rightmargin\listtextrightmargin
            \advance\rightmargin\rightskip
            \advance\leftmargin\leftskip
            \tempdimen\leftmargini
            \advance\tempdimen-\labelsep
            \leftmargin28pt\labelsep4.5pt
            \iffnalpha
               \def\makelabel##1{{\hskip\listlabelleftskip{\csname listdevicefont\romannumeral\the\@enumdepth\endcsname{\iflabelrightalign\hss\fi\textlistlabel##1}}}}%
               \global\fnalphafalse
            \else
               \def\makelabel##1{\hbox to \tempdimen{\hskip\listlabelleftskip{\csname listdevicefont\romannumeral\the\@enumdepth\endcsname\hbox to \enumdimwd{\iflabelrightalign\hss\fi\textlistlabel##1}}}}%
            \fi
         \else
            \ifnum \@enumdepth=2
               \tempdimen\leftmarginii
               \advance\tempdimen-\labelsep
               \def\makelabel##1{\hbox to \tempdimen{\hskip\listlabelleftskipii{\csname listdevicefont\romannumeral\the\@enumdepth\endcsname\hbox to \enumdimwd{\iflabelrightalign\hss\fi##1}}}}%
            \else
               \ifnum \@enumdepth=3
                  \tempdimen\leftmarginiii
                  \advance\tempdimen-\labelsep
                  \def\makelabel##1{\hbox to \tempdimen{\hskip\listlabelleftskipiii{\csname listdevicefont\romannumeral\the\@enumdepth\endcsname\hbox to \enumdimwd{\iflabelrightalign\hss\fi##1}}}}%
               \else
                  \ifnum \@enumdepth=4
                     \tempdimen\leftmarginiv
                     \advance\tempdimen-\labelsep
                     \def\makelabel##1{\hbox to \tempdimen{\hskip\listlabelleftskipiv{\csname listdevicefont\romannumeral\the\@enumdepth\endcsname\hbox to \enumdimwd{\iflabelrightalign\hss\fi##1}}}}%
                  \else
                     \ifnum \@enumdepth=5
                        \tempdimen\leftmarginv
                        \advance\tempdimen-\labelsep
                        \def\makelabel##1{\hbox to \tempdimen{\hskip\listlabelleftskipv{\csname listdevicefont\romannumeral\the\@enumdepth\endcsname\hbox to \enumdimwd{\iflabelrightalign\hss\fi##1}}}}%
                     \else
                        \ifnum \@enumdepth=6
                           \tempdimen\leftmarginvi
                           \advance\tempdimen-\labelsep
                           \def\makelabel##1{\hbox to \tempdimen{\hskip\listlabelleftskipvi{\csname listdevicefont\romannumeral\the\@enumdepth\endcsname\hbox to \enumdimwd{\iflabelrightalign\hss\fi##1}}}}%
                        \else
                           \ifnum \@enumdepth=7
                              \tempdimen\leftmarginvii
                              \advance\tempdimen-\labelsep
                              \def\makelabel##1{\hbox to \tempdimen{\hskip\listlabelleftskipvii{\csname listdevicefont\romannumeral\the\@enumdepth\endcsname\hbox to \enumdimwd{\iflabelrightalign\hss\fi##1}}}}%
                           \else
                              \ifnum \@enumdepth=8
                                 \tempdimen\leftmarginviii
                                 \advance\tempdimen-\labelsep
                                 \def\makelabel##1{\hbox to \tempdimen{\hskip\listlabelleftskipviii{\csname listdevicefont\romannumeral\the\@enumdepth\endcsname\hbox to \enumdimwd{\iflabelrightalign\hss\fi##1}}}}%
                              \else
                                 \ifnum \@enumdepth=9
                                    \tempdimen\leftmarginix
                                    \advance\tempdimen-\labelsep
                                    \def\makelabel##1{\hbox to \tempdimen{\hskip\listlabelleftskipix{\csname listdevicefont\romannumeral\the\@enumdepth\endcsname\hbox to \enumdimwd{\iflabelrightalign\hss\fi##1}}}}%
                                 \else
                                    \ifnum \@enumdepth=10
                                       \tempdimen\leftmarginx
                                       \advance\tempdimen-\labelsep
                                       \def\makelabel##1{\hbox to \tempdimen{\hskip\listlabelleftskipx{\csname listdevicefont\romannumeral\the\@enumdepth\endcsname\hbox to \enumdimwd{\iflabelrightalign\hss\fi##1}}}}%
                                    \else
                                       \def\makelabel##1{\hss\llap{\csname listdevicefont\romannumeral\the\@enumdepth\endcsname##1}}%
                                    \fi
                                 \fi
                              \fi
                           \fi
                        \fi
                     \fi
                  \fi
               \fi
            \fi
         \fi}

   \fi}
%
\def\endenumerate{\@topsepadd\csname belowlistskip\romannumeral\the\@enumdepth\endcsname\endlist}%
%
\newenvironment{arabiclist}{%
   \abovelistskipi12\p@%
   \belowlistskipi12\p@%
   \labelsepi5pt
   \def\theenumi{\arabic{enumi}}
   \def\theenumii{\arabic{enumii}}%
   \def\theenumiii{\arabic{enumiii}}%
   \def\theenumiv{\arabic{enumiv}}%
   \def\theenumv{\arabic{enumv}}%
   \def\theenumvi{\arabic{enumvi}}%
   \def\theenumvii{\arabic{enumvii}}%
   \def\theenumviii{\arabic{enumviii}}%
   \def\theenumix{\arabic{enumix}}%
   \def\theenumx{\arabic{enumx}}%
   \renewcommand\labelenumi{\theenumi.}
   \renewcommand\labelenumii{\theenumii.}
   \renewcommand\labelenumiii{\theenumiii.}
   \begin{enumerate}\leftskip-3pt\itemsep5pt}
      {\end{enumerate}}
%
\def\bullsymfont{\fontfamily{\zpdefault}\fontsize{10}{12}\selectfont}
\def\bullsym{\raise-0.02pt\hbox{\bullsymfont\mycolor{\colorthree o}}}
%
\newenvironment{bulletlist}{%
   \labelsepi6pt
   \def\theenumi{\arabic{enumi}}
   \def\theenumii{\alph{enumii}}%
   \def\theenumiii{\arabic{enumiii}}%
   \def\theenumiv{\arabic{enumiv}}%
   \def\theenumv{\alph{enumv}}%
   \def\theenumvi{\arabic{enumvi}}%
   \def\theenumvii{\arabic{enumvii}}%
   \def\theenumviii{\alph{enumviii}}%
   \def\theenumix{\arabic{enumix}}%
   \def\theenumx{\arabic{enumx}}%
   \renewcommand\labelenumi{\textbullet}
   \renewcommand\labelenumii{\textbullet}
   \renewcommand\labelenumiii{\textbullet}
   \begin{enumerate}\leftskip18pt}
      {\end{enumerate}}
%
\def\learnsymfont{\fontfamily{ams}\fontsize{10}{12}\selectfont}
\def\learnsym{{\learnsymfont\mycolor{\colorseven I}}}
%
\newenvironment{learnbulletlist}{\par\raggedright%
   \hsize\colmargin\linewidth\colmargin
   \labelsepi5pt
   \def\theenumi{\arabic{enumi}}
   \def\theenumii{\alph{enumii}}%
   \def\theenumiii{\arabic{enumiii}}%
   \def\theenumiv{\arabic{enumiv}}%
   \def\theenumv{\alph{enumv}}%
   \def\theenumvi{\arabic{enumvi}}%
   \def\theenumvii{\arabic{enumvii}}%
   \def\theenumviii{\alph{enumviii}}%
   \def\theenumix{\arabic{enumix}}%
   \def\theenumx{\arabic{enumx}}%
   \renewcommand\labelenumi{\learnsym}
   \renewcommand\labelenumii{\learnsym}
   \renewcommand\labelenumiii{\learnsym}
   \begin{enumerate}}
      {\end{enumerate}}
%
\newenvironment{wherelist}{%
   \def\listdevicefonti{\upshape}
   \listtextleftmargin 0pt
   \abovelistskipi13\p@ plus2pt
   \belowlistskipi13\p@ plus2pt
   \begin{enumerate}}
      {\end{enumerate}}
%
\newenvironment{romanlist}{%
   \def\theenumi{\roman{enumi}}\def\theenumii{\roman{enumii}}%
   \def\theenumiii{\roman{enumiii}}\def\theenumiv{\roman{enumiv}}%
   \def\theenumv{\roman{enumv}}\def\theenumvi{\roman{enumvi}}%
   \def\theenumvii{\roman{enumvii}}\def\theenumviii{\roman{enumviii}}%
   \def\theenumix{\roman{enumix}}\def\theenumx{\roman{enumx}}%
   \begin{enumerate}\leftskip8pt}
      {\end{enumerate}}
%
\newenvironment{alphalist}{%
   \itemsepi0pt
   \labelsepi5pt
   \labelsepii5pt
   \labelsepiii5pt
   %\labelrightalignfalse
   \def\theenumi{\alph{enumi}}\def\theenumii{\alph{enumii}}%
   \def\theenumiii{\alph{enumiii}}\def\theenumiv{\alph{enumiv}}%
   \def\theenumv{\roman{enumv}}\def\theenumvi{\roman{enumvi}}%
   \def\theenumvii{\roman{enumvii}}\def\theenumviii{\roman{enumviii}}%
   \def\theenumix{\roman{enumix}}\def\theenumx{\roman{enumx}}%
   \renewcommand\labelenumi{\theenumi.}
   \renewcommand\labelenumii{\theenumii.}
   \renewcommand\labelenumiii{\theenumiii.}
   \begin{enumerate}\leftskip8pt}
      {\end{enumerate}}

%
\newenvironment{fnalphalist}{%
   \abovelistskipi0pt plus2pt
   \belowlistskipi0pt plus2pt
   \itemsepi-2pt
   \labelsepi3.6pt
   \global\fnalphatrue
   \listlabelleftskip\fskip
   \def\theenumi{\alph{enumi}}\def\theenumii{\alph{enumii}}%
   \def\theenumiii{\alph{enumiii}}\def\theenumiv{\alph{enumiv}}%
   \def\theenumv{\roman{enumv}}\def\theenumvi{\roman{enumvi}}%
   \def\theenumvii{\roman{enumvii}}\def\theenumviii{\roman{enumviii}}%
   \def\theenumix{\roman{enumix}}\def\theenumx{\roman{enumx}}%
   \renewcommand\labelenumi{(\theenumi)}
   \begin{enumerate}}
      {\end{enumerate}}
%
\newenvironment{Romanlist}{%
   \def\theenumi{\Roman{enumi}}\def\theenumii{\Roman{enumii}}%
   \def\theenumiii{\Roman{enumiii}}\def\theenumiv{\Roman{enumiv}}%
   \def\theenumv{\roman{enumv}}\def\theenumvi{\roman{enumvi}}%
   \def\theenumvii{\roman{enumvii}}\def\theenumviii{\roman{enumviii}}%
   \def\theenumix{\roman{enumix}}\def\theenumx{\roman{enumx}}%
   \begin{enumerate}}
      {\end{enumerate}}

\newenvironment{Alphalist}{%
   \def\theenumi{\Alph{enumi}}\def\theenumii{\Alph{enumii}}%
   \def\theenumiii{\Alph{enumiii}}\def\theenumiv{\Alph{enumiv}}%
   \def\theenumv{\roman{enumv}}\def\theenumvi{\roman{enumvi}}%
   \def\theenumvii{\roman{enumvii}}\def\theenumviii{\roman{enumviii}}%
   \def\theenumix{\roman{enumix}}\def\theenumx{\roman{enumx}}%
   \begin{enumerate}\leftskip8pt}
      {\end{enumerate}}
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  unnumlist %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
\unnumlistitemindent=0pt
%
\def\@item[#1]{%
   \if@noparitem
      \@donoparitem
   \else
      \if@inlabel
         \indent \par
      \fi
      \ifhmode
         \unskip\unskip \par
      \fi
      \if@newlist
         \if@nobreak
            \@nbitem
         \else
            \addpenalty\@beginparpenalty
            \addvspace\@topsep
            \addvspace{-\parskip}%
         \fi
      \else
         \addpenalty\@itempenalty
         \addvspace\itemsep
      \fi
      \global\@inlabeltrue
   \fi
   \everypar{%
      \@minipagefalse
      \global\@newlistfalse
      \if@inlabel
         \global\@inlabelfalse
         {\setbox\z@\lastbox
            \ifvoid\z@
               \kern-\itemindent
            \fi}%
         \ifunnumlistitem\hspace*{\unnumlistitemindent}\fi\box\@labels
         \penalty\z@
      \fi
      \if@nobreak
         \@nobreakfalse
         \clubpenalty \@M
      \else
         \clubpenalty \@clubpenalty
         \everypar{}%
      \fi}%
   \if@noitemarg
      \@noitemargfalse
      \if@nmbrlist
         \refstepcounter\@listctr
      \fi
   \fi
   \sbox\@tempboxa{\makelabel{#1}}%
   \global\setbox\@labels\hbox{%
      \unhbox\@labels
      \hskip \itemindent
      \hskip -\labelwidth
      \hskip -\labelsep
      \ifdim \wd\@tempboxa >\labelwidth
         \box\@tempboxa
      \else
         \hbox to\labelwidth {\unhbox\@tempboxa}%
      \fi
      \hskip \labelsep}%
   \ignorespaces}
%
\unnumlisttextskip=0pt
\newenvironment{unnumlist}{%
   \unnumlistitemtrue
   \listtextleftmargin\unnumlisttextskip
   \listtextleftmarginii\unnumlisttextskip
   \listtextleftmarginiii\unnumlisttextskip
   \listtextleftmarginiv\unnumlisttextskip
   \listtextleftmarginv\unnumlisttextskip
   \listtextleftmarginvi\unnumlisttextskip
   \listtextleftmarginvii\unnumlisttextskip
   \listtextleftmarginviii\unnumlisttextskip
   \listtextleftmarginix\unnumlisttextskip
   \listtextleftmarginx\unnumlisttextskip
   \labelsepi0pt
   \labelsepii0pt
   \labelsepiii0pt
   \labelsepiv0pt
   \labelsepv0pt
   \labelsepvi0pt
   \labelsepvii0pt
   \labelsepviii0pt
   \labelsepix0pt
   \labelsepx0pt
   \def\theenumi{\arabic{enumi}}
   \def\theenumii{\alph{enumii}}%
   \def\theenumiii{\arabic{enumiii}}%
   \def\theenumiv{\arabic{enumiv}}%
   \def\theenumv{\alph{enumv}}%
   \def\theenumvi{\arabic{enumvi}}%
   \def\theenumvii{\arabic{enumvii}}%
   \def\theenumviii{\alph{enumviii}}%
   \def\theenumix{\arabic{enumix}}%
   \def\theenumx{\arabic{enumx}}%
   \renewcommand\labelenumi{}
   \renewcommand\labelenumii{}
   \renewcommand\labelenumiii{}
   \renewcommand\labelenumiv{}
   \renewcommand\labelenumv{}
   \renewcommand\labelenumvi{}
   \renewcommand\labelenumvii{}
   \renewcommand\labelenumviii{}
   \renewcommand\labelenumix{}
   \renewcommand\labelenumx{}
   \begin{enumerate}\leftskip-15pt\itemsep5pt}
      {\end{enumerate}
   \global\unnumlistitemfalse}
%

\def\itemize{%
   \itemleftmargin12\p@ % won't be active in enumerate
   \itemlabelsep4\p@ % labelsep in itemize for all levels
   \ifnum \@itemdepth >3 \@toodeep\else\ifnum\@enumdepth>0\@itemdepth\@enumdepth\fi \advance\@itemdepth \@ne
      \edef\@itemitem{labelitem\romannumeral\the\@itemdepth}%
      \list{\csname\@itemitem\endcsname}%
      {%
         \topsep\csname abovelistskip\romannumeral\the\@itemdepth\endcsname%\fi
         \itemsep\csname itemsep\romannumeral\the\@itemdepth\endcsname
         \labelsep\itemlabelsep
         \listfont
         \setbox\tempbox\hbox{\csname\@itemitem\endcsname}
         \csname leftmargin\romannumeral\the\@itemdepth\endcsname\wd\tempbox
         \advance\csname leftmargin\romannumeral\the\@itemdepth\endcsname\itemlabelsep
         \ifnum\@itemdepth=\@ne\ifnum\@enumdepth=0 % if not inside an enumerate
               \rightmargin\listtextrightmargin
               \advance\rightmargin\rightskip
               \advance\csname leftmargin\romannumeral\the\@itemdepth\endcsname\itemleftmargin
               \advance\leftmargini\leftskip
            \else
               \advance\csname leftmargin\romannumeral\the\@itemdepth\endcsname\itemleftmargin
               \advance\leftmarginii\leftskip
            \fi\fi
         \leftmargin\csname leftmargin\romannumeral\the\@itemdepth\endcsname
         \def\makelabel##1{\hss\llap{##1}}}

   \fi}%
%
\def\enditemize{%
   \@topsepadd\csname belowlistskip\romannumeral\the\@itemdepth\endcsname%\fi
   \endlist}

\def\description{%
   \descleftmargin17.5\p@ % won't be active in enumerate
   \desclabelsep4\p@ % labelsep in itemize for all levels
   \ifnum \@itemdepth >3 \@toodeep\else\ifnum\@enumdepth>0\@itemdepth\@enumdepth\fi \advance\@itemdepth \@ne
      \edef\@itemitem{labelitem\romannumeral\the\@itemdepth}%
      \list{\csname\@itemitem\endcsname}%
      {%
         \topsep9pt%\fi
         \itemsep5pt
         \labelsep\desclabelsep
         \listfont
         \setbox\tempbox\hbox{\csname\@itemitem\endcsname}
         \csname leftmargin\romannumeral\the\@itemdepth\endcsname\wd\tempbox
         \advance\csname leftmargin\romannumeral\the\@itemdepth\endcsname\desclabelsep
         \ifnum\@itemdepth=\@ne\ifnum\@enumdepth=0 % if not inside an enumerate
               \rightmargin\listtextrightmargin
               \advance\rightmargin\rightskip
               \advance\csname leftmargin\romannumeral\the\@itemdepth\endcsname\descleftmargin
               \advance\leftmargini\leftskip
            \else
               \advance\csname leftmargin\romannumeral\the\@itemdepth\endcsname\descleftmargin
               \advance\leftmarginii\leftskip
            \fi\fi
         \leftmargin\csname leftmargin\romannumeral\the\@itemdepth\endcsname
         \def\makelabel##1{\hss\llap{##1}}}

   \fi}%
%
\def\enddescription{\endlist}
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%% enumroman (i) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
\newenvironment{xbllist}{%
   \abovelistskipii9pt plus2pt%
   \belowlistskipii9pt plus2pt%
   \itemlabelsep12.5\p@%
   \itemsepi0pt
   \def\listfont{}
   \renewcommand\labelitemi{\textbullet}%
   \renewcommand\labelitemii{\textbullet}%
   \renewcommand\labelitemiii{\textbullet}%
   \renewcommand\labelitemiv{\textbullet}%
   \begin{itemize}}
      {\end{itemize}}

\newenvironment{hyphenlist}{%
   \renewcommand\labelitemi{-}%
   \renewcommand\labelitemii{-}%
   \renewcommand\labelitemiii{-}%
   \renewcommand\labelitemiv{-}%
   \begin{itemize}\leftskip-5pt\labelsep5.3pt}
      {\end{itemize}}
%
\newenvironment{asterisklist}{%
   \renewcommand\labelitemi{\textasteriskcentered}%
   \renewcommand\labelitemii{\textasteriskcentered}%
   \renewcommand\labelitemiii{\textasteriskcentered}%
   \renewcommand\labelitemiv{\textasteriskcentered}%
   \begin{itemize}}
      {\end{itemize}}
%
\newenvironment{caselist}{%
   \def\textlistlabel{Case\ }%
   \begin{enumerate}}
      {\end{enumerate}}
%
\newenvironment{steplist}{%
   \def\textlistlabel{Step\ }%
   \begin{enumerate}}
      {\end{enumerate}}
%
\newenvironment{labellist}{%
   \begin{description}}
      {\end{description}}
%
\def\setitemindent#1{\settowidth{\labelwidth}{#1}%
   \let\setit@m=Y%
   \leftmargini\labelwidth
   \advance\leftmargini\labelsep
   \def\@listi{\leftmargin\leftmargini
      \labelwidth\leftmargini\advance\labelwidth by -\labelsep
      \parsep=\parskip
      \topsep=\medskipamount
      \itemsep=\parskip \advance\itemsep by -\parsep}}
\def\setitemitemindent#1{\settowidth{\labelwidth}{#1}%
   \let\setit@m=Y%
   \leftmarginii\labelwidth
   \advance\leftmarginii\labelsep
   \def\@listii{\leftmargin\leftmarginii
      \labelwidth\leftmarginii\advance\labelwidth by -\labelsep
      \parsep=\parskip
      \topsep=6\p@
      \itemsep=\parskip \advance\itemsep by -\parsep}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%% npara %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
\def\NPARfont{}
\newenvironment{npara}{\par%\addvspace{9pt plus2pt}%
   \NPARfont
   %   \hsize\textwidth%27pc
   \setcounter{ncount}{0}%
   \def\item{\par\addtocounter{ncount}{1}\arabic{ncount}.\hskip2.6pt\ignorespaces}}
{\par}%\addvspace{9pt plus2pt}\@endparenv}%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%% splist %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
\def\marginfont{\fontsize{9}{10}\selectfont\bfseries\raggedright}
\newcommand{\comment}[1]{%
   \setlength\overfullrule{0pt}%
   \ifodd\c@page
      \marginpar{%
         \parbox{8pc}{\par\vskip-1.5pt\marginfont please check.\par}}%
      \fboxsep.1pt\fbox{#1}%
   \else
      \marginpar{%
         \parbox{8pc}{\par\vskip-1.5pt\marginfont please check.\par}}
      \fboxsep.1pt\fbox{#1}\fi}
%
%
\setcounter{topnumber}{5}
\renewcommand\topfraction{.9}
\setcounter{bottomnumber}{1}
\renewcommand\bottomfraction{.3}
\setcounter{totalnumber}{5}
\renewcommand\textfraction{.09}
\renewcommand\floatpagefraction{.901}
\setcounter{dbltopnumber}{4}
\renewcommand\dbltopfraction{.9}
\renewcommand\dblfloatpagefraction{.901}
%
\setlength\abovecaptionskip{10.5\p@}
\setlength\belowcaptionskip{3.5\p@}
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  Figures %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
\def\figcaptiondesc#1{\gdef\@figcaptiondesc{#1}}
\figcaptiondesc{}
%
\renewcommand\thefigure{\@arabic\c@figure}
\def\fps@figure{tbp}
\def\ftype@figure{1}
\def\ext@figure{lof}

\def\figurehead#1{\gdef\@figurehead{#1}}\figurehead{}
\def\fnum@figure{\figcaptionnumfont{Figure}~\thefigure}

\newif\ifimage\global\imagefalse

\newenvironment{figure}
{\global\imagetrue\@float{figure}}
{\end@float\global\imagefalse\global\nosidecapfalse}

\def\@float#1{%
   \@ifnextchar[%
   {\@xfloat{#1}}%
   {\edef\reserved@a{\noexpand\@xfloat{#1}[\csname fps@#1\endcsname]}%
      \reserved@a}}
\newenvironment{figure*}
{\@dblfloat{figure}}
{\end@dblfloat}
%
\newenvironment{Figure}
{\par\addvspace{12pt plus2pt}\def\@captype{figure}}
{\par\addvspace{12pt plus2pt}}
%
\newenvironment{Figure*}
{\par\addvspace{12pt plus2pt}\def\@captype{figure}}
{\par\addvspace{12pt plus2pt}}

%
\def\figlabelfont{\fontsize{10}{12}\selectfont}
\def\figlabel#1{\gdef\@figlabel{#1}}
\figlabel{}
%
\figcaptionleftskip0pt
\figcaptionrightskip0pt
\figindent0pt
\figwidthcapdimen12pt
\figleftskip0pt
\figrightskip0pt
\adjustskip0pt
%
\newdimen\figcappush
\newdimen\figcappull
\newbox\figscapbox

\newif\ifnosidecap\global\nosidecapfalse

   \newif\ifnosidecap\global\nosidecapfalse
      \def\sidecapoff{\global\nosidecaptrue}
      \def\swapfig{\global\swapfigtrue}

      \def\figpunct{.}

      \def\figpunct{.}
      \def\@makefigurecaption#1#2{\figcaptionfont%
         \global\setbox\figcapbox\hbox{\figcaptionfont{\figcaptionnumfont#1\figpunct\ }{\figcaptiondescfont\@figcaptiondesc}\hskip\figcapdescsep#2\par}
         \def\capprint{\centerline{\copy\figbox}\vskip\abovecaptionskip\unhbox\figcapbox}%
         \ifnosidecap\capprint\else%
            \ifdim\wd\figbox<245pt%
               \figcappush\wd\figbox%
               \advance\figcappush12pt%
               \leftskip\figcappush%
               \global\setbox\figscapbox\vbox{\unhbox\figcapbox}%
               \copy\figbox%
               \vspace*{-\ht\figscapbox}%
               \unvbox\figscapbox%
               \vspace*{\textfloatsep}%
            \else%
               \capprint%
            \fi\fi}

      \def\ArtDir{fig/}%
      %
      \def\ArtPiece#1{\epsfbox{\ArtDir#1}}%
      %

      \def\fpofigbox#1{\FPtrue\def\@fpo{#1}}
      %
      \def\whiteink{\special{color push cmyk 0 0 0 0.0}}
      \def\blackink{\special{color push cmyk 0 0 0 1.0}}
      %
      \def\@startpbox#1{\vtop\bgroup \setlength\hsize{#1}\@arrayparboxrestore}
      \def\@endpbox{\@finalstrut\@arstrutbox\par\vspace*{-\baselineskip}\egroup\hfil}
      \let\@@startpbox=\@startpbox
      \let\@@endpbox=\@endpbox
      %
      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Styles of Figures
      %
      \sideverticalskip=0pt
      \sidetskip=0pt
      %
      \def\FigName{figure}
      %
      \long\def\@makecaption#1#2{%
         \ifx\FigName\@captype
            \@makefigurecaption{#1}{#2}%
            \vskip0pt
         \else
            \@maketablecaption{#1}{#2}%
            \vskip\belowcaptionskip
         \fi}
      %
      \renewcommand\thetable{\arabic{table}}
      %
      \def\fps@table{tbp}
      \def\ftype@table{2}
      \def\ext@table{lot}
      \def\fnum@table{\tablename\ \thetable.\ }
      %
      \def\tablefootnote#1{
         \global\advance\tfootcount1\expandafter\gdef\csname tablefootnote\the\tfootcount\endcsname{#1}}
      %
      \newenvironment{table}
      {\global\tableshowtrue
         \let\footnote\tablefootnote%
         \@float{table}}
      {\end@float\global\tableshowfalse\gdef\@tbnote{}}
      %
      \def\tablebelowspace#1{\gdef\@tablebelowspace{#1}}\tablebelowspace{}
      %
      \newenvironment{table*}
      {\let\footnote\tablefootnote%%
         \@dblfloat{table}}
      {%
         \ifx\@tablebelowspace\@empty%
         \else%
            \vspace*{\@tablebelowspace}\tablebelowspace{}%
         \fi%
         \end@dblfloat\global\tablefootnotenonefalse\global\killtableabovespacefalse}
      %
      \newenvironment{intexttable}
      {\begin{table}[h]}
            {\end{table}}
      %
      \gdef\base{10pt}
      \gdef\colbase{10pt}
      %
      \newenvironment{Table}
      {\par\addvspace{12pt plus2pt}\def\@captype{table}}
      {\par\addvspace{12pt plus2pt}}
      %
      \newenvironment{boxtextTable}[1][\relax]%
      {\par\addvspace{12pt plus2pt}\def\@captype{table}}
      {\par\addvspace{12pt plus2pt}}
      %
      \newenvironment{Table*}
      {\par\addvspace{12pt plus2pt}\def\@captype{table}}
      {\par\addvspace{12pt plus2pt}}
      %
      \def\tableabovespace#1{\gdef\@tableabovespace{#1}}\tableabovespace{}
      %
      \def\tnumspace{\hbox{\ }}
      \def\tspace{\\[-4pt]}
      %
      \def\tablecontinued{{\fontsize{7.5}{10}\bfseries\itshape\selectfont (Continued)}}
      \def\tableexplanation#1{\itshape\selectfont #1}
      \def\tableexplanationskip{\hskip8.5pt}
      %
      \def\tablefig#1{\gdef\@tablefig{#1}}\tablefig{des-tableshade}
      %
      \overfullrule0pt
      %
      \tablenumcapsep=2.5pt
      %
      \def\tablecolshade#1#2#3#4{%
         \vbox to 0pt{\parindent0pt\vspace*{#2pt}\vspace*{-7.8pt}\hbox to 0pt{\vbox{\hspace*{#1pt}\hspace*{-6pt}\hbox{\vcolor{\grayten\vrule height#3pt width#4pt depth0pt}}}}}}%
      %
      \def\tableshade#1{\gdef\@tableshade{#1}}\tableshade{0pt}%
      \def\tableruleheight#1{\gdef\@tableruleheight{#1}}\tableruleheight{138pt}%
      %
      %
      \def\tablenum{\tablecaptionnumfont\uppercase{Table}~\thetable}

      \def\tbnote#1{\gdef\@tbnote{#1\par}}\tbnote{}%


      \definecolor{tabcolgray}{cmyk}{0,0,0,0.40}
      \definecolor{tabbodygray}{cmyk}{0,0,0,.10}

      \def\@maketablecaption#1#2{
         \setbox\tabcapbox\vbox{{\tablecaptionfont\ifunnumtable\else\noindent{\tablecaptionnumfont#1}\fi\hskip\tablenumcapsep%
                  #2\vphantom{y}\par}}
         \ifdim\ht\tabcapbox<19pt
            \centering{\tablecaptionfont\ifunnumtable\else\noindent{\tablecaptionnumfont#1}\fi\hskip\tablenumcapsep%
               #2\vphantom{y}\par}\tablefont\global\unnumtablefalse%
         \else
            {\tablecaptionfont\ifunnumtable\else\noindent{\tablecaptionnumfont#1}\fi\hskip\tablenumcapsep%
               #2\vphantom{y}\par}\tablefont\global\unnumtablefalse%
         \fi}
      %
      %
      %
      \def\TCH#1{\TCHfont#1}%
      %
      \def\x{@{\extracolsep{\fill}}}
      %
      %\def\hhrulefill{\hbox\bgroup\leavevmode\leaders\hrule\hfill\kern\z@\egroup}
      %%
      %
      %%%%%%%%%%%%%%%% B-Table Rules %%%%%%%%%%%%%%
      %
      \newenvironment{tabnote}{\@par\tabnotefont\vphantom{y}\vskip-5pt\@par}
      {}
      %



      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  Math %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
      %
      \setlength\arraycolsep{1.5\p@}
      \setlength\tabcolsep{6\p@}
      \setlength\arrayrulewidth{.29\p@}
      \setlength\doublerulesep{2\p@}
      \setlength\tabbingsep{\labelsep}
      \setlength\fboxsep{3\p@}
      \setlength\fboxrule{.4\p@}
      %
      \setlength\columnsep{14.3\p@}
      \setlength\columnseprule{0\p@}
      %
      \@addtoreset{equation}{chapter}
      \renewcommand\theequation{\arabic{equation}}

      %\def\text#1{\hbox{\scriptsize #1}}%
      \def\text#1{\mathchoice
         {\hbox{\fontsize{\tf@size}{\tf@size}\selectfont#1}}%
         {\hbox{\fontsize{\tf@size}{\tf@size}\selectfont#1}}%
         {\hbox{\fontsize{\sf@size}{\sf@size}\selectfont#1}}%
         {\hbox{\fontsize{\ssf@size}{\ssf@size}\selectfont#1}}}
      %
      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  Footnote %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

      \renewcommand\footnoterule{%
         \kern-3\p@
         \hrule\@height0.5pt\@width60pt%
         \kern4.5\p@}

      \@addtoreset{footnote}{chapter}

      \foot@parindent10pt

      \newcommand\@makefntext[1]{%
         \ifpddata%
         \else%
            \ifFoottext%
            \else%
               %    \vskip-5pt
            \fi\fi%
         \noindent
         \hb@xt@\foot@parindent{\hss{\@makefnmark}}#1}

      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  End Footnote %%%%%%%%%%%%%%%%%%%%%%%%%%%%
      %
      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  Page styles  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
      \def\oddfolio{{\foliofont\thepage}}
      \def\evenfolio{{\foliofont\thepage}}
      %
      \def\versorh#1{\gdef\@versorh{#1}}\versorh{}
      \def\rectorh#1{\gdef\@rectorh{#1}}\rectorh{}

      \def\jrntitle#1{\gdef\@jrntitle{#1}}\jrntitle{PASA}%
      \def\oddfolio{{\foliofont\thepage}}
      \def\evenfolio{{\foliofont\thepage}}
      %
      \def\lefttitle#1{\gdef\@versorh{#1}}\lefttitle{}
      \def\righttitle#1{\gdef\@rectorh{{\it#1}}}\righttitle{}
      %
      \def\ps@headings{%
         \let\@oddfoot\@empty%
         \let\@evenfoot\@empty%
         \def\@oddhead{%
            \hbox to \typewidth{\hfill{\rhfont\@rectorh}\hspace*{20pt}{\oddfolio}}%
         }%
         \def\@evenhead{%
            \hbox to \textwidth{{\evenfolio}\hspace*{20pt}{\rhfont\@versorh}\hfill}%
         }%
         \let\@mkboth\markboth
         \def\chaptermark##1{\markboth{\@versorh}{\@rectorh}}%
         %    \def\sectionmark##1{\markright{##1}}%
      }%
      %
      \def\mrhfont{\fontfamily{\sfdefault}\fontsize{9}{9}\selectfont}

      \def\ps@mtochead{%
         \let\@oddfoot\@empty%
         \let\@evenfoot\@empty%
         \def\@oddhead{%
            \hbox to \typewidth{{\mrhfont\contentsname}\hfill{\moddfolio}}%
         }%
         \def\@evenhead{%
            \hbox to \textwidth{{\mevenfolio}\hfill{\mrhfont\contentsname}}%
         }%
         \let\@mkboth\markboth
         \def\chaptermark##1{\markboth{\@versorh}{\@rectorh}}%
         %    \def\sectionmark##1{\markright{##1}}%
      }

      \def\mfoliofont{\fontfamily{\sfdefault}\fontsize{9}{9}\selectfont}

      \def\moddfolio{{\mfoliofont\thepage}}

      \def\mevenfolio{{\mfoliofont\thepage}}

      \def\ps@mtocopen{%
         \let\@evenfoot\@empty%
         \def\@oddfoot{%
            \vbox to 4pt{\hbox to \textwidth{\hfill{\moddfolio}\hfill}}}
         \def\@oddhead{\relax}%
         \def\@evenhead{\relax}%
         \let\@mkboth\markboth
         \def\chaptermark##1{\markboth{\@versorh}{\@rectorh}}}
      %
      \def\ps@empty{%
         \def\@oddfoot{}%
         \let\@evenfoot\@oddfoot
         \def\@evenhead{}%
         \def\@oddhead{}%
         \let\@mkboth\markboth
         \let\chaptermark\@gobble
         \let\sectionmark\@gobble}

      \def\ps@rotatepage{%
         \def\@oddfoot{\hfill\oddfolio\hfill}%
         \def\@evenfoot{\hfill\evenfolio\hfill}
         \def\@evenhead{}%
         \def\@oddhead{}%
         \let\@mkboth\markboth
         \let\chaptermark\@gobble
         \let\sectionmark\@gobble}

      %
      \def\logo@Image@path{../Figures/Logo/LaTeX-Logo/}
      %%%%%%%%%%%%%%%%%%%%%%%% Proof Readers Template  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
      \font\QEDlogofont=msam10 at 10.7pt
      \def\QEDlogo{\hbox{\QEDlogofont\char'003}}
      \def\QEDblogo{\hbox{\QEDlogofont\char'004}}
      \def\sqbox{{\QEDlogofont\char'004}}
      \def\prbox{\unskip\hskip4.5pt\ignorespaces{\fboxsep0pt\fbox{\vrule width5pt height5pt depth0pt}}\global\logofalse}
      \def\@proof[#1]{\noindent{\itshape#1.\hskip9.5pt}\ignorespaces}
      \ptdraftrule0pt
      %%%%%%%%%%%%%%%%%%%%%%%% Proof Readers Template  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
      %
      \ptdraftrule0pt
      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  Bibliography Section   %%%%%%%%%%%%%%%%%%

      \def\surname#1{#1}
      \def\givenname#1{#1}
      \def\middlename#1{#1}
      \def\pubname#1{#1}
      \def\corporate#1{#1}
      \def\booktitle#1{#1}
      \def\jmonth#1{#1}
      \def\articletitle#1{#1}
      \def\edition#1{#1}
      \def\firstpage#1{#1}
      \def\lastpage#1{#1}
      \def\issue#1{#1}
      \def\volume#1{#1}
      \def\bibyear#1{#1}
      \def\jaddress{\unskip,\ }

      \def\comma{,}
      \def\fullstop{.}
      \def\nocomma{\def\comma{\unskip\ignorespaces}}
      \def\nofullstop{\def\fullstop{}}

      \def\equationnumber#1{\gdef\@equationnumber{#1}}\equationnumber{}%

      %%%%% TRUE FOR CHAPTER TITLE AND FALSE FOR SECTION TITLE %%%%%%%%
      %%%%%%%% Unnumberd References %%%%%%%%%%%
      \setlength\bibleftmargin  {11pt}
      \setlength\bibitemsep  {0pt}
      \setlength\bibparsep  {0pt}
      %%%%%%%% Numbered Within Squre Bracket %%%%%%%%%%%
      \setlength\biblabelsep  {10pt}
      \setlength\bibleftmargini  {5.75pt}
      %%%%%%%% Numbered With Dot %%%%%%%%%%%%%%%
      \def\firstsectionhead{\vspace*{8.7pt}\bibitem{}\ \vspace*{-20pt}}
      \setlength\bibtext  {5pt}
      %
      %%%%%%%% Unnumberd References %%%%%%%%%%%
      \setlength\bibleftmargin{27pt}
      \setlength\bibitemsep  {0pt}
      \setlength\bibparsep  {0pt}
      %%%%%%%% Numbered Within Squre Bracket %%%%%%%%%%%
      \setlength\biblabelsep  {10pt}
      \setlength\bibleftmargini  {5.75pt}
      %%%%%%%% Numbered With Dot %%%%%%%%%%%%%%%
      \def\firstsectionhead{\vspace*{8.7pt}\bibitem{}\ \vspace*{-20pt}}
      \setlength\bibtext  {5pt}
      %
      \def\referenceheadfont{\fontsize{8.6}{10.5}\selectfont\centering}

      \newif\ifreferences\global\referencesfalse%

         \newdimen\bibindent
         \setlength\bibindent{1.5em}
         \def\bibfont{\fontsize{8}{10}\selectfont}
         \newenvironment{thebibliography}[1]
         {\global\referencestrue\section*{\bibname}%
            \bibfont\list{\@biblabel{\@arabic\c@enumiv}}{%
               \settowidth\labelwidth{\@biblabel{#1}}%
               \leftmargin\labelwidth
               \advance\leftmargin\labelsep
               \@openbib@code
               \usecounter{enumiv}%
               \let\p@enumiv\@empty
               \renewcommand\theenumiv{\@arabic\c@enumiv}}%
            \sloppy
            \clubpenalty4000
            \@clubpenalty \clubpenalty
            \widowpenalty4000%
            \sfcode`\.\@m}
         {\def\@noitemerr
            {\@latex@warning{Empty `thebibliography' environment}}%
            \endlist}
         \let\@openbib@code\@empty
         \newcommand\newblock{}
         %
         %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  End Bibliography Section %%%%%%%%%%%%%%%%
         %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% TOC  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
         %
         \def\@tochead#1{\thispagestyle{empty}%
            \vbox{\vspace*{6.6pc}
               \noindent{\fontsize{12}{12}\selectfont #1\endgraf}}\vspace*{4pc}}
         %
         \newcommand\tableofcontents{%
            \UnicodeCharacter{13}{\ignorespaces}%
            \let\l@title\l@chapter%
            \let\l@section\l@ctocsection%
            \let\l@subsection\l@ctocsubsection%
            \@tochead{\contentsname}%
            \markboth{\contentsname}{\contentsname}%
            \vspace*{-1.65mm}%%%%\vspace*{-4.28mm}%modified on 30-05-2009 to get the first line align to 13th line
            \@starttoc{toc}%
            \UnicodeCharacter{13}{ \ignorespaces}}%
         %% LIST OF FIGURES%
         \newcommand\listoffigures{%
            \setlength\overfullrule{\z@}%
            \chapter*{\listfigurename}%
            \markboth{\listfigurename}{\listfigurename}%
            \@starttoc{lof}}%
         %% LIST OF TABLES %%
         \newcommand\listoftables{%
            \setlength\overfullrule{\z@}%
            \chapter*{\listtablename}%
            \markboth{\listtablename}{\listtablename}%
            \@starttoc{lot}}%
         %
         \newcommand\@pnumwidth{.5pc}%
         \newcommand\@tocrmarg{2em}%
         \newcommand\@minitocrmarg{1.5pc}%
         \newcommand\@dotsep{4.5}%
         \setcounter{tocdepth}{1}%
         %%
         \def\fmbmcontentfont{}%
         \def\fmbmcontentpagefont{}%
         %%
         \fixfmbmcontentwidth=\z@%
         %%
         \newcommand\l@fmbm[2]{%
         {\par%
         \iffirstfm\vspace*{\z@}\else\vskip\z@\fi%
         \iffirstbm\vskip13.1\p@\else\fi%
         \noindent\rightskip\@pnumwidth\parfillskip-\@pnumwidth%
         \ifdottedfmbmcontent%
            {\fmbmcontentfont#1}%
            \nobreak\leaders\hbox{$\m@th\mkern\@dotsep mu\hbox{.}\mkern\@dotsep mu$}\hfill\nobreak%
            \hb@xt@\@pnumwidth{\hfil{\ifstartfm{\it page\ }\fi{\fmbmcontentpagefont#2}}}\par%
      \else%
         \noindent\@hangfrom{\hbox to \fixfmbmcontentwidth{}}%
         {\fmbmcontentfont#1}\hfill{\ifstartfm{\it page\ }\fi{\fmbmcontentpagefont#2}}\par%
   \fi}%
   \global\firstfmfalse%
   \global\startfmfalse%
   \global\firstbmfalse}%
   %% Author contentsline %%
   \def\authorcontentfont{\ifmergetoc\fontsize{10}{12}\selectfont\itshape\leftskip\z@\rightskip5pc plus1fill{}\else\fontsize{10}{12}\selectfont\bfseries\leftskip\z@\rightskip5pc plus1fill{}\fi}%
   %%
   \fixauthorcontentwidth=\z@%
   %%
   \newcommand\l@author[2]{%
   {\par%
   \iffixauthorcontent%
      \rightskip\@pnumwidth\parfillskip -\@pnumwidth%
      \noindent\@hangfrom{\hbox to \authorcontentwidth{}}%
   \else%
      \rightskip\@tocrmarg%
      \advance\rightskip by\z@\@plus2cm%
      \parfillskip-\@tocrmarg%
      \noindent\@hangfrom{\hbox to \authorcontentwidth{}}%
   \fi%
   {\authorcontentfont#1}%
   \ifmergetoc\else\nobreak\leaders\hbox{$\m@th\mkern\@dotsep mu\hbox{.}\mkern\@dotsep mu$}\fi\hfill\nobreak%
   \ifmergetoc\else\hb@xt@\@pnumwidth{\hfil\chapcontentpagefont\iffirstproof 000\else#2\fi}\fi\par}}%
   %% Chapter contentsline %
   %%
   \def\chapcontentnumfont{\fontsize{10}{12}\bfseries\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   \def\chapcontentfont{\fontsize{10}{12}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   \def\chapcontentpagefont{\fontsize{10}{12}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   %%
   \def\chappunct#1{\gdef\@chappunct{#1}}\chappunct{}%
   %%
   \newcommand\chpmax[1]{%
      \setbox\tempbox\hbox{\chapcontentnumfont#1\@chappunct}%
      \global\chapwidth\wd\tempbox}%
   %%
   \def\chapnumberline#1{\ifswitch@CH@bkm@no#1\quad\else\hb@xt@\@tempdima{\hbox to \chapwidth{\hfill\chapcontentnumfont#1\@chappunct}\hfil}\fi}%
   %%
   \fixchapcontentwidth=\z@%
   \enspacechapcontentwidth=1em%
   %%
   \newcommand\l@chapter[2]{%
      \overfullrule\z@%
      \par\addvspace{12\p@}%
      \let\numberline\chapnumberline%
      \ifnum\c@tocdepth >\m@ne%
         \iffirstfm\vskip \z@\else\vskip 13\p@\fi%
         \global\firstfmtrue%
         \global\firstbmtrue%
         \iffixchapcontent%
            \setlength\@tempdima{\fixchapcontentwidth}%
         \else%
            \setlength\@tempdima{\chapwidth}%
            \advance\@tempdima\enspacechapcontentwidth%
         \fi%
         \ifdottedchapcontent%
            \begingroup%
            \parindent\z@%
            \rightskip\@tocrmarg%
            \advance\rightskip by\z@\@plus2cm%
            \parfillskip-\@tocrmarg%
            \leavevmode%
            %           \advance\leftskip\@tempdima%
            %            \hskip-\leftskip%
            {\chapcontentfont#1}%
            \penalty\@highpenalty%
            \endgroup%
         \else%
            \begingroup%
            \parindent\z@%
            %\rightskip\@pnumwidth plus1fill%
            %\parfillskip-\@pnumwidth%
            \leavevmode%
            \advance\leftskip\@tempdima%
            \hskip-\leftskip%
            \noindent{\chapcontentfont#1\par}%
            \vskip-\baselineskip%
            %\nobreak\hfil %
            \nobreak\hbox to\textwidth{\chapcontentpagefont\hss #2}\par%
            \penalty\@highpenalty%
            \endgroup%
         \fi%
         \vskip\z@%
      \fi}%
   %%
   %% CTOC Section contentsline %%
   %%
   \def\minitocsectioncontentnumfont{\fontsize{8.5}{10}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   \def\ctocsectioncontentnumfont{\fontsize{10}{12}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   \def\ctocsectioncontentfont{\fontsize{10}{12}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   \def\ctocsectioncontentpagefont{\fontsize{10}{12}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   %%
   \def\ctocsectionpunct#1{\gdef\@ctocsectionpunct{#1}}\ctocsectionpunct{}%
   %%
   \newcommand\ctocsecmax[1]{%
      \setbox\tempbox\hbox{\ctocsectioncontentnumfont#1\@ctocsectionpunct}%
      \@ctocsecmaxnumdim\wd\tempbox%
      \global\ctocsecnwidth\wd\tempbox}%
   %%
   \newcommand\sectmax[1]{%
      \setbox\tempbox\hbox{\ctocsectioncontentnumfont#1\@ctocsectionpunct}%
      \@secmaxnumdim\wd\tempbox%
      \global\secnwidth\wd\tempbox}%
   %%
   \def\ctocsecnumberline#1{%
      \hb@xt@\@tempdima{%
         \hbox to \ctocsecnwidth{%
            \hfill\hb@xt@\@ctocsecmaxnumdim{\ctocsectioncontentnumfont#1\@ctocsectionpunct\hfil}\hfil}}}%
   %%
   \def\minitocsecnumberline#1{%
      \hb@xt@\@tempdima{%
         \hbox to \ctocsecnwidth{%
            \hfill\hb@xt@\@ctocsecmaxnumdim{\minitocsectioncontentnumfont#1\@ctocsectionpunct\hfil}\hfil}}}%
   %%
   \ctocfixsectioncontentwidth=\z@%
   \ctocenspacesectioncontentwidth=1em%
   %%
   \newcommand\l@ctocsection[2]{}%
   \newcommand\l@subsubsection[2]{}%
   \newcommand\l@paragraph[2]{}%
   %% CTOC Subsection contentsline %%
   \def\minitocsubsectioncontentnumfont{\fontsize{8.5}{10}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   \def\ctocsubsectioncontentnumfont{\fontsize{10}{12}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   \def\ctocsubsectioncontentfont{\fontsize{10}{12}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   \def\ctocsubsectioncontentpagefont{\fontsize{10}{12}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   %%
   \def\ctocsubsectionpunct#1{\gdef\@ctocsubsectionpunct{#1}}\ctocsubsectionpunct{}%
   %%
   \newcommand\ctocsubsecmax[1]{%
      \setbox\tempbox\hbox{\ctocsubsectioncontentnumfont#1\@ctocsubsectionpunct}%
      \@ctocsubsecmaxnumdim\wd\tempbox%
      \global\ctocsubsecnwidth\wd\tempbox}%
   %%
   \newcommand\subsectmax[1]{%
      \setbox\tempbox\hbox{\ctocsubsectioncontentnumfont#1\@ctocsubsectionpunct}%
      \@subsecmaxnumdim\wd\tempbox%
      \global\subsecnwidth\wd\tempbox}%
   %%
   \def\ctocsubsecnumberline#1{%
      \hb@xt@\@tempdima{\hbox to \ctocsubsecnwidth{\hfill\hb@xt@\@ctocsubsecmaxnumdim{\ctocsubsectioncontentnumfont#1\@ctocsubsectionpunct\hfill}}\hfil}}%
   %%
   \def\minitocsubsecnumberline#1{%
      \hb@xt@\@tempdima{\hbox to \ctocsubsecnwidth{\hfill\hb@xt@\@ctocsubsecmaxnumdim{\minitocsubsectioncontentnumfont#1\@ctocsubsectionpunct\hfill}}\hfil}}%
   %%
   \ctocfixsubsectioncontentwidth=\z@%
   \ctocenspacesubsectioncontentwidth=1em%
   %%
   \newcommand\l@ctocsubsection[2]{%
      \ifmono%
         \overfullrule\z@%
         \par\addvspace{\z@}%
         \let\numberline\ctocsubsecnumberline%
         \ifnum\c@tocdepth >\m@ne%
            \iffirstfm\vskip \z@\else\vskip 13\p@\fi%
            \global\firstfmtrue%
            \global\firstbmtrue%
            \ifctocfixsubsectioncontent%
               \setlength\@tempdima{\ctocfixsubsectioncontentwidth}%
            \else%
               \setlength\@tempdima{\subsecnwidth}%
               \advance\@tempdima\ctocenspacesubsectioncontentwidth%
            \fi%
            \ifctocdottedsubsectioncontent%
               \begingroup%
               \parindent\z@%
               \rightskip\@tocrmarg%
               \advance\rightskip by\z@\@plus2cm%
               \parfillskip-\@tocrmarg%
               \leavevmode%
               \advance\leftskip\@tempdima%
               \hskip-\leftskip%
               \advance\leftskip\chapwidth%
               \advance\leftskip\enspacechapcontentwidth%
               \advance\leftskip\secnwidth%
               \advance\leftskip\ctocenspacesectioncontentwidth%
               {\ctocsubsectioncontentfont#1\unskip}%
               \nobreak\leaders\hbox{$\m@th\mkern\@dotsep mu\hbox{.}\mkern\@dotsep mu$}\hfill\nobreak%
               \hb@xt@\@pnumwidth{\hfil\ctocsectioncontentpagefont#2}\par%
               \penalty\@highpenalty%
               \endgroup%
            \else%
               \begingroup%
               \parindent\z@%
               %\rightskip\@pnumwidth plus1fill%
               \parfillskip-\@pnumwidth%
               \leavevmode%
               \advance\leftskip\@tempdima%
               \hskip-\leftskip%
               \noindent{\ctocsubsectioncontentfont#1\par}%
               \vskip-\baselineskip%
               %\nobreak\hfil%
               \nobreak\hbox to\textwidth{\ctocsubsectioncontentpagefont\hss #2}\par%
               \penalty\@highpenalty%
               \endgroup%
            \fi%
            \vskip\z@%
         \fi%
      \fi}%
   %% Figure contentsline %%
   \def\figurecontentnumfont{\fontsize{10}{12}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   \def\figurecontentfont{\fontsize{10}{12}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   \def\figurecontentpagefont{\fontsize{10}{12}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   %%
   \def\figurepunct#1{\gdef\@figurepunct{#1}}\figurepunct{}%
   %%
   \newcommand\figmax[1]{%
      \setbox\tempbox\hbox{\figurecontentnumfont#1\@figurepunct}%
      \@figuremaxnumdim\wd\tempbox%
      \global\figurecontwidth\wd\tempbox%
      \advance\figurecontwidth\enspacefigurecontentwidth}%
   %%
   \def\figurenumberline#1{\hb@xt@\@tempdima{\hbox to \figurecontwidth{\figurecontentnumfont#1\@figurepunct\hfill}\hfil}}%
   %%
   \fixfigurecontentwidth=\z@%
   \enspacefigurecontentwidth=6\p@%
   %%
   \newcommand\l@figure[2]{%
      \overfullrule\z@%
      \par\addvspace{\z@}%
      \let\numberline\figurenumberline%
      \ifnum\c@tocdepth >\m@ne%
         \iffirstfm\vskip \z@\else\vskip 13\p@\fi%
         \global\firstfmtrue%
         \global\firstbmtrue%
         \iffixfigurecontent%
            \setlength\@tempdima{\fixfigurecontentwidth}%
         \else%
            \setlength\@tempdima{\figurecontwidth}%
            \advance\@tempdima\enspacefigurecontentwidth%
         \fi%
         \ifdottedfigurecontent%
            \begingroup%
            \parindent\z@%
            \rightskip\@tocrmarg%
            \advance\rightskip by\z@\@plus2cm%
            \parfillskip-\@tocrmarg%
            \leavevmode%
            \advance\leftskip\@tempdima%
            \hskip-\leftskip%
            {\figurecontentfont#1}%
            \nobreak\leaders\hbox{$\m@th\mkern\@dotsep mu\hbox{.}\mkern\@dotsep mu$}\hfill\nobreak%
            \hb@xt@\@pnumwidth{\hfil\figurecontentpagefont#2}\par%
            \penalty\@highpenalty%
            \endgroup%
         \else%
            \begingroup%
            \parindent\z@%
            \rightskip\@pnumwidth plus1fill%
            \parfillskip-\@pnumwidth%
            \leavevmode%
            \advance\leftskip\@tempdima%
            \hskip-\leftskip%
            \noindent{\figurecontentfont#1\par}%
            \vskip-\baselineskip%
            %\nobreak\hfil%
            \nobreak\hbox to\textwidth{\figurecontentpagefont\hss #2}\par%
            \penalty\@highpenalty%
            \endgroup%
         \fi%
         \vskip\z@%
      \fi}%
   %% Table contentsline %%
   \def\tablecontentnumfont{\fontsize{10}{12}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   \def\tablecontentfont{\fontsize{10}{12}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   \def\tablecontentpagefont{\fontsize{10}{12}\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%
   %
   \def\tablepunct#1{\gdef\@tablepunct{#1}}\tablepunct{}%
   %%
   \newcommand\tabmax[1]{%
      \setbox\tempbox\hbox{\tablecontentnumfont#1\@tablepunct}%
      \@tablemaxnumdim\wd\tempbox%
      \global\tablecontwidth\wd\tempbox%
      \advance\tablecontwidth\enspacetablecontentwidth}%
   %%
   \def\tablenumberline#1{\hb@xt@\@tempdima{\hbox to \tablecontwidth{\tablecontentnumfont#1\@tablepunct\hfill}\hfil}}%
   %%
   \fixtablecontentwidth=\z@%
   \enspacetablecontentwidth=6\p@%
   %%
   \newcommand\l@table[2]{%
      \overfullrule\z@%
      \par\addvspace{\z@}%
      \let\numberline\tablenumberline%
      \ifnum\c@tocdepth >\m@ne%
         \iffirstfm\vskip \z@\else\vskip 13\p@\fi%
         \global\firstfmtrue%
         \global\firstbmtrue%
         \iffixtablecontent%
            \setlength\@tempdima{\fixtablecontentwidth}%
         \else%
            \setlength\@tempdima{\tablecontwidth}%
            \advance\@tempdima\enspacetablecontentwidth%
         \fi%
         \ifdottedtablecontent%
            \begingroup%
            \parindent\z@%
            \rightskip\@tocrmarg%
            \advance\rightskip by\z@\@plus2cm%
            \parfillskip-\@tocrmarg%
            \leavevmode%
            \advance\leftskip\@tempdima%
            \hskip-\leftskip%
            {\tablecontentfont#1}%
            \nobreak\leaders\hbox{$\m@th\mkern\@dotsep mu\hbox{.}\mkern\@dotsep mu$}\hfill\nobreak%
            \hb@xt@\@pnumwidth{\hfil\tablecontentpagefont#2}\par%
            \penalty\@highpenalty%
            \endgroup%
         \else%
            \begingroup%
            \parindent\z@%
            \rightskip\@pnumwidth plus1fill%
            %\parfillskip -\@pnumwidth%
            \leavevmode%
            \advance\leftskip\@tempdima%
            \hskip -\leftskip%
            \noindent{\tablecontentfont#1\par}%
            \vskip-\baselineskip%
            %\nobreak\hfil%
            \nobreak\hbox to\textwidth{\tablecontentpagefont\hss #2}\par%
            \penalty\@highpenalty%
            \endgroup%
         \fi%
         \vskip\z@%
      \fi}%
   %
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  End FM  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %
   \def\Copyright{\leavevmode\fontsize{6.5}{11}\selectfont{\ooalign{\hfil\raise-.25pt\hbox{\fontsize{5}{11}\selectfont C\hskip.5pt}%
            \hfil\crcr\mathhexbox20D}}}
   %
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  Appendix  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %

   \newcommand\appendix{\global\appendixtrue\setcounter{section}{0}}
   %
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% End Appendix %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %
   %
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  Index  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %
   \def\alphabet#1{\par\vskip.5\baselineskip{\bf#1}\par\vskip.5\baselineskip}
   %
   \def\indmatter#1{\gdef\@indmatter{#1}}
   \indmatter{}
   %
   \newenvironment{theindex}{\cleardoublepage%
      \columnseprule \z@
      \columnsep 12\p@
      \markboth{\indexname}{\indexname}
      \tempdimen\normalbaselineskip
      \advance\tempdimen-\baselineskip
      \twocolumn[\@makeschapterhead{\indexname}\vskip\tempdimen\vskip3pt
         \ifx\@indmatter\@empty\else\noindent{\indexfont\@indmatter\par\vskip\baselineskip}\fi%
      ]%
      \thispagestyle{plain}
      \parindent\z@\indexfont
      \let\item\@idxitem}
   {\par\indmatter{}}
   \newcommand\@idxitem  {\par\hangindent3em}
   \newcommand\subitem   {\par\hangindent3em\hspace*{1em}}
   \newcommand\subsubitem{\par\hangindent3em\hspace*{2em}}
   \newcommand\indexspace{\par \vskip\baselineskip}
   %%%%%%%%%%%%%%%%%%%% File Version  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   \ifprinter
      \def\draftnote{\vphantom{\vbox to 0pt{\vskip-12pt
               \hbox{\ \footnotesize\jobname\vphantom{pq}\qquad\jobtag\qquad\today\qquad\currenttime\qquad Char Count= \@TotalChars
                  \ifmathtif\else\@questionmark\fi\hfil}}}%
      \def\comment{}
      \def\Qauthor#1{}
      \def\QtoAuthor#1{}
      \def\QtoClient#1{}
      \def\QtoQC#1{}
      \def\QtoGL#1{}
      \def\qtoa#1{}
   \else
      \def\draftnote{\vbox to 0pt{\vskip-12pt}}%
      \def\Qauthor#1{\marginpar{{\raggedright\footnotesize\bf #1\endgraf}}}

   \fi
   \let\qtoa\Qauthor
   %%%%%%%%%%%%%%%%%%%% Character count  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %
   \def\gray{\special{color push cmyk 0 0 0 0.5}}
   \def\@questionmark{\vbox to 0pt{\rotatebox{40}{\hbox to \textwidth{
                  \begin{picture}(0,0)\put(-340,-50){
                        \fontsize{90}{90}\selectfont Compile Again}\end{picture}\hss}}}}
   \def\questionmark#1{\xdef\@questionmark{#1}}%
   %
   \def\@TotalChars{}
   \def\TotalChars#1{\xdef\@TotalChars{#1}}%
   %
   \def\cropmarks{\nointerlineskip\vbox to 0pt{\offinterlineskip\vss
            \hbox to \trimwidth{\vbox to 0pt{\draftnote}\hfill}}}%

   \def\croprules{%
      \nointerlineskip\vbox to 0pt{\offinterlineskip
            \vskip4pt\cropmarks
            \vskip\topmargin
            \hbox to \trimwidth{\hskip\@themargin\hbox to \textwidth{\hss%
                  \vrule height0pt depth\typeheight width.1pt%
                  \vrule height.1pt depth0pt width\textwidth
                  \vrule height0pt depth\typeheight width.1pt\hss}}%
            \hbox to \trimwidth{\hskip\@themargin\hbox to \textwidth{\hss%
                  \vrule height.1pt depth0pt width\textwidth\hss}\hss}}}
   %
   \gdef\@placewidthart{}
   %
   \figwidth0pt
   \figheight0pt
   %
   \def\authorname{}
   \def\jobno{}
   \def\chapno{}
   %
   \def\changeh#1.#2pt{}
   %
   \def\ArtPiece#1#2#3{%
      \fboxrule.1pt
      \fboxsep0pt
      \oldfigwidth\figwidth
      \gdef\figtemp{#1}%
      %  \addtocounter{figure}{1}
      %%%% for scaling
      \gdef\figtempscale{#3}%\ifx\figtempscale\empty\figtempcount100\else\figtempcount\figtempscale\fi\multiply\figtempcount10
      %%%% to add to figheight
      \setbox\tempbox=\vbox{\epsfbox{\ArtDir#1}}%
      \figheight\ht\tempbox
      %%%% to add to figwidth
      \setbox\tempbox=\hbox{\epsfbox{\ArtDir#1}}%
      \advance\figwidth\wd\tempbox
      \presentfigwidth\wd\tempbox
      \remainingtextwidth\textwidth
      \advance\remainingtextwidth-\oldfigwidth
      \advance\remainingtextwidth-\presentfigwidth
      \tempdim\oldfigwidth\advance\tempdim\presentfigwidth
      %\ifdim\tempdim>\textwidth\par\vskip6pt \figwidth0pt
      \ifdim\remainingtextwidth<0pt\par\vskip6pt %\figwidth0pt
      \else
         %%%% testing whether line is full
      \fi
      \setbox\tempbox=\hbox{\fbox{\epsfbox{\ArtDir#1}\hss}}%
      \xdef\@placewidthart{\@placewidthart\unhbox\tempbox}%
      \leavevmode\vbox{\hsize\presentfigwidth\parindent0pt\leftskip0pt plus1fill\rightskip\leftskip{}
         \@placewidthart\par
         \vskip3pt
         %      Fig. #2\par
         Figure: \figtemp\par
         Reduction: \figtempscale\%\par
         Height:\the\figheight\par
         Width: \the\presentfigwidth\par
         \jobno\quad \chapno \quad\authorname}\unskip\hskip10pt}
   %
   %%%%%%%%%%%%%%%%%%% End File Version %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Trimmarks  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %
   \def\trimmarks{%
      \vbox to 0pt{%
            \vskip-25pt\parindent0pt
            \draftnote\offinterlineskip}%
      \ifdraft
         \vbox to 0pt{\hsize\trimwidth\offinterlineskip
               \parindent0pt\leftskip0pt\rightskip0pt
               \fboxsep0pt\fboxrule\draftrule
               \fbox{\vbox{\vskip\trimheight\hskip\trimwidth}}}%
         %
         \vbox to 0pt{\hsize\trimwidth\offinterlineskip
               \parindent0pt\leftskip0pt\rightskip0pt
               \vbox to \trimheight{\offinterlineskip\parindent0pt
                  \hbox to \trimwidth{\vbox to 2pc{\vskip-3.5pc\hbox{\vrule height2pc width\trimrule}}\raisebox{2pc}{\hbox{\hskip-3.5pc\vrule width2pc height\trimrule}}\hfill
                     \raisebox{2pc}{\vrule width2pc height\trimrule\hskip-3.75pc}
                     \vbox to 2pc{\vskip-3.5pc\hbox{\vrule height2pc width\trimrule}}%
                  }\vfill
                  \hbox to \trimwidth{\hbox{\hskip-3.5pc\vrule height\trimrule width2pc}\vbox to 3pc{\vspace*{4.5pc}\hbox{\hskip1.5pc\vrule width\trimrule height2pc}}\hfill
                     \vbox to 3.5pc{\vskip5pc\hbox{\vrule height2pc width\trimrule}}\rlap{\hskip1.5pc\vrule width2pc height\trimrule}}}}%
         %
      \else
         \vbox to 0pt{\hsize\trimwidth\offinterlineskip
         \parindent0pt\leftskip0pt\rightskip0pt
         \vbox to \trimheight{\offinterlineskip\parindent0pt
         \ifregistermark
            \vbox to 0pt{\vspace*{-43.35pt}\hbox to \trimwidth{\hss\epsfbox{\ArtDir logo-02.eps}\hss}}
         \fi
         \hbox to \trimwidth{\vbox to 2pc{\vskip-3.5pc\hbox{\vrule height2pc width\trimrule}}\raisebox{2pc}{\hbox{\hskip-3.5pc\vrule width2pc height\trimrule}}\hfill
            \raisebox{2pc}{\vrule width2pc height\trimrule\hskip-3.75pc}
            \vbox to 2pc{\vskip-3.5pc\hbox{\vrule height2pc width\trimrule}}%
         }\vfill
         \ifregistermark{\hbox to \trimwidth{\hskip-43pt\epsfbox{\ArtDir logo-01.eps}\hfill\epsfbox{\ArtDir logo-01.eps}\hskip-43pt}}\fi
      \vfill
      \hbox to \trimwidth{\hbox{\hskip-3.5pc\vrule height\trimrule width2pc}%
         \vbox to 3pc{\vspace*{4.5pc}\hbox{\hskip1.5pc\vrule width\trimrule height2pc}}\hfill
         \vbox to 3.5pc{\vskip5pc\hbox{\vrule height2pc width\trimrule}}\rlap{\hskip1.5pc\vrule width2pc height\trimrule}}
      \ifregistermark\vbox to 0pt{\vspace*{18.15pt}\hbox to \trimwidth{\hss\epsfbox{\ArtDir logo-02.eps}\hss}}\fi
   }}
\fi
\insidedraftrules}
%
\def\insidedraftrules{\vbox to 0pt{%
         \offinterlineskip\parindent0pt
         \vskip \topmargin
         \tempdimen\normaltextheight
         \advance\tempdimen\headheight
         \advance\tempdimen\headsep
         \moveright\@themargin
         \vbox{\vbox to 0pt{\vskip\headheight\vskip\headsep
                  \vrule height\draftrule width\textwidth}
            \hbox{\fboxsep0pt\fboxrule\draftrule
               \fbox{\vbox to \tempdimen
                  {\hsize\textwidth\hskip\textwidth}}}}}}%
%
\def\insidedraftrules{\overfullrule0pt%
   \iffloutsidemargin
      %  \addtolength\evensidemargin{-\colmargin}
      \addtolength\oddsidemargin{0pt}
   \fi
   \ifflinsidemargin
      \addtolength\evensidemargin{-\colmargin}
      \addtolength\oddsidemargin{\colmargin}
   \fi
   \ifflinsidetexttypewidthsep
      \addtolength\oddsidemargin{\texttypewidthsep}
      \addtolength\evensidemargin{-\texttypewidthsep}
   \fi
   \ifflleftsidemargin
      %  \addtolength\evensidemargin{-2pc}
      \addtolength\oddsidemargin{\colmargin}
   \fi
   \ifflleftsidetexttypewidthsep
      %  \addtolength\evensidemargin{-2pc}
      \addtolength\oddsidemargin{\texttypewidthsep}
   \fi
   \ifflrightsidemargin
      \addtolength\evensidemargin{-\colmargin}
   \fi
   \ifflrightsidetexttypewidthsep
      \addtolength\evensidemargin{-\texttypewidthsep}
   \fi
   \vbox to 0pt{%
         \offinterlineskip\parindent0pt
         \vskip \topmargin
         \tempdimen\normaltextheight
         \advance\tempdimen\headheight
         \advance\tempdimen\headsep
         \advance\tempdimen-0.4pt
         \moveright\@themargin
         \ifodd\c@page
            \hbox to \textwidth{\hss\hbox to \typewidth{%
                  \vbox to \tempdimen{\hrule height\draftrule
                     \vbox to 0pt{\vskip\headheight\vskip\headsep%\vskip-6pt
                           %\hbox{\vrule height\draftrule width\typewidth}
                        }%
                     \hbox to \typewidth{\vrule width\draftrule
                        \hfill\vrule height\tempdimen width\draftrule%
                        \iffloutsidetexttypewidthsep%
                           \hskip\texttypewidthsep\vrule height\tempdimen width\draftrule\hskip-.3pt%
                        \fi%
                        \iffloutsidemargin%
                           \hskip\colmargin\vrule height\tempdimen width\draftrule\hskip-.3pt%
                        \fi%
                        \ifflinsidetexttypewidthsep%
                           \hskip\texttypewidthsep\vrule height\tempdimen width\draftrule%
                        \fi%
                        \ifflinsidemargin%
                           \hskip\textwidth\hskip-.5pt\vrule height\tempdimen width\draftrule%
                        \fi%
                        \ifflleftsidetexttypewidthsep%
                           \hskip\texttypewidthsep\hskip0pt\vrule height\tempdimen width\draftrule%
                        \fi%
                        \ifflleftsidemargin%
                           \hskip\textwidth\hskip-.5pt\vrule height\tempdimen width\draftrule%
                        \fi%
                        \ifflrightsidetexttypewidthsep%
                           \hskip\texttypewidthsep\vrule height\tempdimen width\draftrule\hskip-.5pt%
                        \fi%
                        \ifflrightsidemargin%
                           \hskip\colmargin\vrule height\tempdimen width\draftrule\hskip-.3pt%
                        \fi%
                     }%
                     \hrule height\draftrule}}%
               \iffloutsidemargin%
                  \hskip-\colmargin%
               \fi%
               \iffloutsidetexttypewidthsep%
                  \hskip-\texttypewidthsep%
               \fi%
               \ifflinsidemargin%
                  %        \hskip-\colmargin%
               \fi%
               \ifflleftsidemargin%
                  %        \hskip-\colmargin%
               \fi%
               \ifflrightsidemargin%
                  \hskip-\colmargin%
               \fi%
               \ifflrightsidetexttypewidthsep%
                  \hskip-\texttypewidthsep%
               \fi%
            }%
         \else%
            \hbox to \textwidth{\hss\hbox to \typewidth{%
                  \vbox to \tempdimen{\hrule height\draftrule%
                     \vbox to 0pt{\vskip\headheight\vskip\headsep%\vskip-6pt
                           %\hbox{\vrule height\draftrule width\typewidth}%
                        }%
                     \hbox to \typewidth{\vrule width\draftrule%
                        \hfill\vrule height\tempdimen width\draftrule%
                        \iffloutsidetexttypewidthsep%
                           \hskip\texttypewidthsep\vrule height\tempdimen width\draftrule%
                        \fi%
                        \iffloutsidemargin%
                           \hskip\textwidth\hskip-.5pt\vrule height\tempdimen width\draftrule%
                        \fi%
                        \ifflinsidetexttypewidthsep%
                           \hskip\texttypewidthsep\vrule height\tempdimen width\draftrule%
                        \fi%
                        \ifflinsidemargin%
                           \hskip\colmargin\ifflinsidetexttypewidthsep\hskip-.3pt\fi\vrule height\tempdimen width\draftrule\hskip-.3pt%
                        \fi%
                        \ifflleftsidetexttypewidthsep%
                           \hskip\texttypewidthsep\hskip0pt\vrule height\tempdimen width\draftrule%
                        \fi%
                        \ifflleftsidemargin%
                           \hskip\textwidth\hskip-.5pt\vrule height\tempdimen width\draftrule%
                        \fi%
                        \ifflrightsidetexttypewidthsep%
                           \hskip\texttypewidthsep\vrule height\tempdimen width\draftrule\hskip-.5pt%
                        \fi%
                        \ifflrightsidemargin%
                           \hskip\colmargin\vrule height\tempdimen width\draftrule\hskip-.3pt%
                        \fi%
                     }%
                     \hrule height\draftrule}}%
               \iffloutsidemargin%
                  %        \hskip-\colmargin%
               \fi%
               \ifflinsidemargin%
                  \hskip-\colmargin%
               \fi%
               \ifflinsidetexttypewidthsep
                  \hskip-\texttypewidthsep%
               \fi
               \ifflleftsidemargin%
                  %        \hskip-\colmargin%
               \fi%
               \ifflrightsidemargin%
                  \hskip-\colmargin%
               \fi%
               \ifflrightsidetexttypewidthsep%
                  \hskip-\texttypewidthsep%
               \fi%
            }%
         \fi}}%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% End Trimmarks  %%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Output Routine  %%%%%%%%%%%%%%%%%%%%%%%%%%
%
\def\@outputpage{%
   \begingroup           % the \endgroup is put in by \aftergroup
   \let \protect \noexpand
   \@resetactivechars
   \@parboxrestore
   \shipout \vbox{%
      \set@typeset@protect
      \aftergroup \endgroup
      \aftergroup \set@typeset@protect
      % correct? or just restore by ending
      % the group?
      \if@specialpage
         \global\@specialpagefalse\@nameuse{ps@\@specialstyle}%
      \fi
      \if@twoside
         \ifodd\count\z@ \let\@thehead\@oddhead \let\@thefoot\@oddfoot
            \let\@themargin\oddsidemargin
         \else \let\@thehead\@evenhead
            \let\@thefoot\@evenfoot \let\@themargin\evensidemargin
         \fi
      \fi
      \reset@font
      \normalsize
      \normalsfcodes
      \let\label\@gobble
      \let\index\@gobble
      \let\glossary\@gobble
      \baselineskip\z@skip \lineskip\z@skip \lineskiplimit\z@
      \@begindvi\trimmarks
      \vskip \topmargin
      \moveright\@themargin \vbox {%
         \setbox\@tempboxa \vbox to\headheight{%
            \vfil
            \color@hbox
            \normalcolor
            \hb@xt@\textwidth{\@thehead}%
            \color@endbox
         }%                        %% 22 Feb 87
         \dp\@tempboxa \z@
         \box\@tempboxa
         \vskip \headsep
         \box\@outputbox
         \baselineskip \footskip
         \color@hbox
         \normalcolor
         \hb@xt@\textwidth{\@thefoot}%
         \color@endbox
      }%
   }%
   \global \@colht \textheight
   \stepcounter{page}%
   \let\firstmark\botmark
}
%
%%%%%%%%%%%%%%%%%%%%%%%% Misc. %%%%%%%%%%%%%%%%%%%%%%%
%
\def\@@question#1{\hbox to \hsize{\hfill
      \rlap{\hskip\marginparsep
         \vbox to 0pt{\hsize\marginparwidth
               \footnotesize
               \raggedright#1\endgraf\vss}}}}
\def\@question#1{\ifvmode
      \@@question{#1}%
   \else
      \vadjust{\vbox to 0pt{%
               \vskip-7.5pt\@@question{#1}\vskip7.5pt}}

   \fi}
%
\def\QtoAuthor#1{\@question{{\bf Author:\ #1}}}
\def\QtoClient#1{\@question{{\bf Client/PM:\ #1}}}
\def\QtoQC#1{\@question{{\bf QC:\ #1}}}
\def\QtoGL#1{\@question{{\bf GL:\ #1}}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% End Output Routine  %%%%%%%%%%%%%%%%%%%%%%
%
\def\spreadlong#1{\ifodd\c@page\wlog{Ignoring spreadlong}
   \else
      \spreadlongtrue\gdef\@spreadlong{#1}%
      \enlargethispage{#1}%
   \fi}
% check specs and enable one or both of these commands
\def\leaflong#1{\enlargethispage{#1}}
%
%%%%%%%%%%%%%%%%%%%%%%%%% Initialization  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
\pagestyle{headings}%
\pagenumbering{arabic}      % Arabic page numbers
\medmuskip=3.5mu
\thickmuskip=3.5mu
\thinmuskip=3.5mu
\frenchspacing
\sloppy%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% To set center in the page %%%%%%%%%%%%%%%%

\advance\voffset-82pt%
\advance\hoffset-72.1pt%

\clubpenalty10000\widowpenalty10000\hyphenpenalty=50%
%
\def\endash{--}
%

\ifonline
   \usepackage{hyperref}%
   \usepackage[all]{hypcap}
   \hypersetup{
      draft=false,
      colorlinks=true,
      linkcolor=blue,
      anchorcolor=blue,
      citecolor=blue,
      urlcolor=blue,
      filecolor=blue,
      bookmarksopenlevel=3,
      bookmarksopen=true,
      pdfborderstyle={/S/U/W 0},
      pdfstartview={FitH 800},
      breaklinks=true}
   \usepackage{url}
   \urlstyle{tt}
   \usepackage{bookmark}[2011/12/02]
   \usepackage{etoolbox}
\else
\fi
\def\linkref#1#2{\ifonline\textcolor{blue}{\hyperlink{#1}{#2}}\else#2\fi}
\def\linktarget#1#2{\ifonline\hypertarget{#1}{#2}\else#2\fi}

\def\acom#1{%
   \global\advance\acomcount1%
   \expandafter\protected@xdef\csname acom\the\acomcount\endcsname{#1}}%

\def\imagestyle#1{\ifx\XML@parent\eqtag\else#1\fi}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% E-Query Definition %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%\ifpuretex
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% E-TeX Definition %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%\usepackage{TeX-Definition}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% B-TeX Definition %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%\else
%\ifmathtif
%\else
%\newread\CharCountread
%      \catcode`\�0
%      \catcode`\�14
%      \catcode`\�1
%      \catcode`\�2
%      \catcode`\�=11
%      \catcode`\�=11
%\xdef\@EndChar{ �}%
%\xdef\@@EndChar{�}%
%\def\PAR{\par}%
%\ifcountempty
%   \gdef\@CharCount{}%
%\else
%\long\gdef\@CharCount{%
%   \openin\CharCountread=\jobname.tex
%   \bgroup
%      \let\do\@makeother\dospecials
%      �loop�ifeof�CharCountread�else
%         �read�CharCountread to �OneLine
%         �ifx�OneLine�PAR
%         �else
%            �CharCounttoks�expandafter��OneLineհ
%            �long�edef�@CharCountTemp��noexpand�@@CharCount�the�CharCounttoks ����@CharCountTemp
%         �fi
%         �wlog��the�TotalCharCount�
%      �repeat
%  �egroup
%   \closein\CharCountread}
%\fi
%%
%\long\gdef\@@CharCount#1#2�{%
%   \def\@tempa{#2}%
%   \def\@tempb{#1}%
%   \ifx\@tempa\@EndChar
%      \let\next\relax
%   \else
%      \ifx\@tempb\@@EndChar
%         \let\next\relax
%      \else
%         \global\advance\TotalCharCount1
%         \long\def\next{\@@CharCount#2�}%
%      \fi
%   \fi
%   \next}
%\fi\fi
%
%%%%%%%%%%%%%%%%%%%%%%%%%% For table column alignments thorughout the journals %%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\hbadness=10000
\vbadness=10000
\brokenpenalty=10000
\doublehyphendemerits=1000000
\finalhyphendemerits=1000000
\clubpenalty=10000
\widowpenalty=10000
\lefthyphenmin=3
\righthyphenmin=3
\uchyph=0

%%%%%%%%%%%%%%%%%%%%%%%%% For table column alignments thorughout the journals %%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\ifpuretex
\else
   \newcommand\emptyfloatpage{\thisfloatpagestyle{rotatepage}}

\fi


\def\spanrule#1{\\[-7pt]#1\\[-5pt]}
%
\def\LT@makecaption#1#2#3{%%
   \LT@mcol\LT@cols c{\addtocounter{table}{-1}%
         \hbox to\z@{%
            \hss\parbox[t]\LTcapwidth{%%
               \sbox\@tempboxa{\Set@LT@caption{#1}{#2}{#3}}%%
               \ifdim\wd\@tempboxa>\hsize%%
                  \Set@LT@caption{#1}{#2}{#3}%%
               \else%%
                  %\hbox to\hsize{\hss\box\@tempboxa\hss}%%
                  \Set@LT@caption{#1}{#2}{\centering#3}

               \fi%%
               \endgraf%
               \vskip\belowcaptionskip%
               \vskip-2\p@}\hss}}}%
%%
\gdef\do@cont@cap{{\tablecaptionnumfont \tablename\ \thetable}\break \LTtablecaptionfont {Continued}}%


%%%%%%%%%%% Font Definition Begin %%%%%%%%%%%%%%%%%%%%%%%
%
\gdef\do@cont@cap{{\tablecaptionnumfont \tablename\ \thetable}\break \LTtablecaptionfont ({\it Continued})}%
%
\def\Dheadeditor#1{\gdef\@Dheadeditor{#1}}\Dheadeditor{}
%
\def\@TiTle{}
%
\def\bkrtitle#1{\gdef\@bkrtitle{#1}}\bkrtitle{\ifruninchapter\else\@in@supertitle\fi}
%
\def\toctltlfont{\fontsize{10}{12}\bfseries\selectfont\rightskip0pt plus 1fill{}\leftskip0pt plus 1fill{}}
\def\tocvolfont{\fontfamily{\rmdefault}\fontsize{10}{10}\selectfont\rightskip0pt plus 1fill{}\leftskip0pt plus 1fill{}}
\def\tocconfont{\fontsize{10}{12}\bfseries\selectfont\rightskip0pt plus 1fill{}\leftskip0pt plus 1fill{}}
%
\def\toctitle#1{\gdef\@toctitle{#1}}\toctitle{}

\def\tocvolume#1{\gdef\@tocvolume{Volume\ #1}}
\def\tocissue#1{\gdef\@tocissue{Number\ #1}}

\def\tocvolumes#1{\gdef\@tocvolumes{Volumes\ #1}}
\def\tocissues#1{\gdef\@tocissues{Numbers\ #1}}

\def\tocyear#1{\gdef\@tocyear{#1}}\tocyear{2010}
%
\def\@tochead#1{\thispagestyle{empty}%
   \vbox{\vspace*{-32.5pt}
      {\toctltlfont \@toctitle\par\vskip14pt}
      {\tocvolfont {\ifx\@tocvolume\undefined\else\@tocvolume\fi\ifx\@tocvolumes\undefined\else\@tocvolumes\fi}, {\ifx\@tocissue\undefined\else\@tocissue\fi\ifx\@tocissues\undefined\else\@tocissues\fi}, {\@tocyear}\par\vskip12pt}
      \noindent{\tocconfont#1\endgraf}}\vskip10.5pt}

\renewcommand\tableofcontents{%
   \UnicodeCharacter{13}{\ignorespaces}
   \let\l@title\l@chapter%
   \let\l@section\l@ctocsection%
   \let\l@subsection\l@ctocsubsection%
   \@tochead{\contentsname}%
   \markboth{\contentsname}{\contentsname}%
   \vspace*{-1.65mm}%%%%\vspace*{-4.28mm}%modified on 30-05-2009 to get the first line align to 13th line
   \@starttoc{toc}%
   \UnicodeCharacter{13}{ \ignorespaces}}%

\def\chapcontentfont{\fontsize{10}{12}\selectfont}%
\def\chapcontentpagefont{\fontsize{10}{12}\bfseries\selectfont\leftskip\z@\rightskip\z@ plus1fill{}}%

\renewcommand*\l@chapter[2]{%
   \ifnum \c@tocdepth >\m@ne
      \par\addvspace{6\p@}%
      \setlength\@tempdima{2em}%
      \begingroup
      \parindent \z@
      \rightskip\@tocrmarg
      %%      \parfillskip -\@pnumwidth
      %%      \leavevmode
      {\chapcontentfont#1\par}
      \addpenalty{-\@highpenalty}%
      \penalty\@highpenalty
      \endgroup
   \fi}
%
\newcommand*\l@part[2]{%
   \ifnum \c@tocdepth >\m@ne
      \par\addvspace{12\p@}%
      \setlength\@tempdima{2em}%
      \begingroup
      \parindent \z@
      \rightskip\@tocrmarg
      %%      \parfillskip -\@pnumwidth
      %%      \leavevmode
      {\chapcontentfont\underline{#1}\par}\vspace*{2pt}
      \addpenalty{-\@highpenalty}%
      \penalty\@highpenalty
      \endgroup
   \fi}
%
\renewcommand\@pnumwidth{14pt}%
%
\renewcommand\l@author[2]{%
{%
\par%
\iffixauthorcontent%
   \rightskip\@pnumwidth\parfillskip -\@pnumwidth%
   \noindent\@hangfrom{\hbox to \authorcontentwidth{}}%
\else%
   \rightskip\@tocrmarg%
   \advance\rightskip by\z@\@plus2cm%
   \parfillskip-\@tocrmarg%
   \noindent\@hangfrom{\hbox to \authorcontentwidth{}}%
\fi%
{\authorcontentfont#1\kern-3pt}%
\nobreak\leaders\hbox{$\m@th\mkern\@dotsep mu\hbox{.}\mkern\@dotsep mu$}\hfill\nobreak%
\hb@xt@\@pnumwidth{\hss\chapcontentpagefont#2\par}\par}}%
%%%
\def\aulabel{Au:\ }

%%%%%%%%%%%%%%%% For Table %%%%%%%%%
\usepackage{arydshln}
\usepackage{booktabs}
\setlength\dashlinedash{0.2pt}
\setlength\dashlinegap{.51pt}
\setlength\arrayrulewidth{0.3pt}
\def\hdashline{\\[-12pt]\adl@hdashline\adl@ihdashline\\[-11.1pt]}
\def\adl@vrule#1{\hb@xt@ #1pt{\hss\fontsize{3.5}{3.5}\selectfont.\hss}\relax}

\newdimen\belowmidrulesep
\newdimen\midlightrulewidth

\heavyrulewidth=.5pt
\lightrulewidth=.25pt
\midlightrulewidth=.30pt
\cmidrulewidth=.5pt
\belowrulesep=.65ex
\belowmidrulesep=.83ex
\belowbottomsep=0pt
\aboverulesep=.4ex
\abovetopsep=0pt
\cmidrulesep=\doublerulesep
\cmidrulekern=.5em
\defaultaddspace=.5em

\def\midrule{\noalign{\ifnum0=`}\fi
   \@aboverulesep=\aboverulesep
   \global\@belowrulesep=\belowmidrulesep
   \global\@thisruleclass=\@ne
   \@ifnextchar[{\@BTrule}{\@BTrule[\midlightrulewidth]}}

\renewcommand{\arraystretch}{1.42}

\ifpuretex
   \def\gt{>}
   \def\lt{<}
\else
\fi

\newenvironment{abstract}{\global\Abstracttrue%
   \global\setbox\abstractbox\vbox
   \bgroup\absfont
   \setlength\parindent{0pt}\leftskip9pt\rightskip9pt}
{\egroup}
%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\email}[1]{\href{mailto:#1}{\color{blue}#1}}

\def\ackheadfont{\fontfamily{\sfdefault}\fontsize{8}{10}\selectfont\bfseries}
\def\ackfont{\fontsize{8}{10}\selectfont}

\newenvironment{acknowledgements}{\@par\addvspace{8pt}\noindent{\ackheadfont\ackname.\ }\ackfont}{\@par\addvspace{7pt}}

\newcommand{\xmlpi}[1]{#1}{}


\def\tra#1#2{{\spaceskip#1pt plus1pt minus1pt #2}}


%%%%%%%figure sidecaption%%%%%%%%%%
\newbox\figbox
\newdimen\figheight%

\renewcommand\@makefntext[1]{%
   \ifpddata%
   \else%
      \ifFoottext%
      \else%
         %    \vskip-5pt
      \fi\fi%
   \noindent
   \hb@xt@\foot@parindent{\hss{\@makefnmark}}#1}

\renewcommand\thefootnote{\@alph\c@footnote}%

\usepackage[authoryear]{natbib}
\def\bibfont{\fontsize{8}{10}\selectfont}
\renewenvironment{thebibliography}[1]{%
   \bibsection
   \parindent\z@
   \bibpreamble
   \bibfont
   \list{\@biblabel{\the\c@NAT@ctr}}{\@bibsetup{#1}\global\c@NAT@ctr\z@}%
   \ifNAT@openbib
      \renewcommand\newblock{\par}%
   \else
      \renewcommand\newblock{\hskip .11em \@plus.33em \@minus.07em}%
   \fi\itemsep0pt\itemindent-9pt\leftskip-1pt
   \sloppy\clubpenalty4000\widowpenalty4000
   \sfcode`\.\@m
   \let\NAT@bibitem@first@sw\@firstoftwo
   \let\citeN\cite \let\shortcite\cite
   \let\citeasnoun\cite
}{%
   \bibitem@fin
   \bibpostamble
   \def\@noitemerr{%
      \PackageWarning{natbib}{Empty `thebibliography' environment}%
   }%
   \endlist
   \bibcleanup
}%
%
\@namedef{tabular*}#1{\tablefont%
   \setlength\dimen@{#1}%
   \edef\@halignto{to\the\dimen@}\tablefont\@tabular}

\newcommand{\undersim}[1]{\mathrel{\mathpalette\@undersim{#1}}}
\newcommand{\@undersim}[2]{%
   \vcenter{%
      \ialign{%
         ##\cr
         $\m@th#1#2$\cr
         \noalign{\nointerlineskip\kern.2ex}
         $\m@th#1\sim$\cr
         \noalign{\kern-.4ex}
      }%
   }%
}
\newcommand{\gsim}{\undersim{>}}
\newcommand{\lsim}{\undersim{<}}

\patchcmd{\NAT@citex}
{\@citea\NAT@hyper@{%
      \NAT@nmfmt{\NAT@nm}%
      \hyper@natlinkbreak{\NAT@aysep\NAT@spacechar}{\@citeb\@extra@b@citeb}%
      \NAT@date}}
{\@citea\NAT@nmfmt{\NAT@nm}%
   \NAT@aysep\NAT@spacechar\NAT@hyper@{$\NAT@date$}}{}{}

% Patch case where name and year are separated by opening bracket
\patchcmd{\NAT@citex}
{\@citea\NAT@hyper@{%
      \NAT@nmfmt{\NAT@nm}%
      \hyper@natlinkbreak{\NAT@spacechar\NAT@@open\if*#1*\else#1\NAT@spacechar\fi}%
      {\@citeb\@extra@b@citeb}%
      \NAT@date}}
{\@citea\NAT@nmfmt{\NAT@nm}%
   \NAT@spacechar\NAT@@open\if*#1*\else#1\NAT@spacechar\fi\NAT@hyper@{$\NAT@date$}}
{}{}


\def\ggsim{\protect\gsim}
\def\llsim{\protect\lsim}

%\font\mtsyfont = mtsy at 5.35pt
%\newcommand\sast{\hbox{\mtsyfont\char'003}}

\def\linenumberfont{\reset@font\normalfont\fontsize{6}{8}\selectfont}

%\patchcmd{\@mn@margintest}{\@tempswafalse}{\@tempswatrue}{}{}
%\patchcmd{\@mn@margintest}{\@tempswafalse}{\@tempswatrue}{}{}


%%%%%%%%Author Color%%%%%%%%
\definecolor{snamecol}{rgb}{1,.64,1}

\usepackage{proof}
\newtheoremstyle{theormstyle}% hnamei
{12.5pt}% hSpace abovei
{12.5pt}% hSpace belowi
{\it}% hBody fonti
{0pt}% hIndent amounti1
{\bfseries}% hTheorem head fonti
{.}% hPunctuation after theorem headi
{5pt}% hSpace after theorem headi2
{}% hTheorem head spec (can be left empty, meaning �normal�)i
\theoremstyle{theormstyle}
\newtheorem*{theorem}{Theorem}
\newtheorem{therm}{Theorem}
\newtheorem{proposition}[therm]{Proposition}
\newtheorem{corollary}[therm]{Corollary}
\newtheorem{result}[therm]{Result}
\newtheorem{definition}[therm]{Definition}
\newtheorem{lemma}[therm]{Lemma}
\newtheorem{notation}[therm]{Notation}
\newtheorem{claim}{Claim}

\newtheoremstyle{remarkstyle}% hnamei
{12.5pt}% hSpace abovei
{12.5pt}% hSpace belowi
{}% hBody fonti
{0pt}% hIndent amounti1
{\normalfont\bfseries}% hTheorem head fonti
{.}% hPunctuation after theorem headi
{5pt}% hSpace after theorem headi2
{}% hTheorem head spec (can be left empty, meaning �normal�)i
\theoremstyle{remarkstyle}

\newtheorem{remark}[therm]{Remark}

\newtheorem*{remark*}{Remark}


\thm@bodyfont{\itshape}
\thm@headfont{\bfseries}

\def\confltxtfont{\fontsize{8}{10}\selectfont}
\newenvironment{confl}{\@par\addvspace{5.5pt}\noindent{\ackheadfont {Conflict of interest.}}}{\@par\addvspace{7pt}\confltxtfont}

\newcommand{\orcid}[1][]{\iffinals\includegraphics{CUP_orcid_logo_Print}\else\href{https://orcid.org/#1}{\includegraphics{CUP_orcid_logo_Web}}\fi}%%%%%%%%%%%%%%

\def\endcteinfo#1{\gdef\@endcteinfo{\vfill\noindent\rotatebox{90}{\rule{0.5pt}{60pt}}\@@par%
      \fontsize{8}{10}\selectfont\noindent{\bf Cite this article:} #1}
}\endcteinfo{}%

\def\endctxt#1{\@endcteinfo{#1\@@par}}

\patchcmd{\@mn@margintest}{\@tempswafalse}{\@tempswatrue}{}{}
\patchcmd{\@mn@margintest}{\@tempswafalse}{\@tempswatrue}{}{}

\def\unnumfig#1{\@par\addvspace{6pt}\centerline{#1}\@par\addvspace{6pt}}

%%%%%%%End note links%%%%%%%%%%%%%%%%%%%%
%%% hyperendnotes.sty
\makeatletter
\newif\ifenotelinks
\newcounter{Hendnote}
\let\savedhref\href
\let\savedurl\url
\def\endnotemark{%
\@ifnextchar[\@xendnotemark{%
   \stepcounter{endnote}%
   \protected@xdef\@theenmark{\theendnote}%
   \protected@xdef\@theenvalue{\number\c@endnote}%
   \@endnotemark
}%
}%
\def\@xendnotemark[#1]{%
   \begingroup\c@endnote#1\relax
   \unrestored@protected@xdef\@theenmark{\theendnote}%
   \unrestored@protected@xdef\@theenvalue{\number\c@endnote}%
   \endgroup
   \@endnotemark
}%
\def\endnotetext{%
\@ifnextchar[\@xendnotenext{%
   \protected@xdef\@theenmark{\theendnote}%
   \protected@xdef\@theenvalue{\number\c@endnote}%
   \@endnotetext
}%
}%
\def\@xendnotenext[#1]{%
   \begingroup
   \c@endnote=#1\relax
   \unrestored@protected@xdef\@theenmark{\theendnote}%
   \unrestored@protected@xdef\@theenvalue{\number\c@endnote}%
   \endgroup
   \@endnotetext
}%
\def\endnote{%
\@ifnextchar[\@xendnote{%
   \stepcounter{endnote}%
   \protected@xdef\@theenmark{\theendnote}%
   \protected@xdef\@theenvalue{\number\c@endnote}%
   \@endnotemark\@endnotetext
}%
}%
\def\@xendnote[#1]{%
   \begingroup
   \c@endnote=#1\relax
   \unrestored@protected@xdef\@theenmark{\theendnote}%
   \unrestored@protected@xdef\@theenvalue{\number\c@endnote}%
   \show\@theenvalue
   \endgroup
   \@endnotemark\@endnotetext
}%
\def\@endnotemark{%
\leavevmode
\ifhmode
   \edef\@x@sf{\the\spacefactor}\nobreak
\fi
\ifenotelinks
   \expandafter\@firstofone
\else
   \expandafter\@gobble
\fi
{%
\Hy@raisedlink{%
   \hyper@@anchor{Hendnotepage.\@theenvalue}{\empty}%
}%
}%
\hyper@linkstart{link}{Hendnote.\@theenvalue}%
\makeenmark
\hyper@linkend
\ifhmode
   \spacefactor\@x@sf
\fi
\relax
}%
\long\def\@endnotetext#1{%
   \if@enotesopen
   \else
      \@openenotes
   \fi
   \immediate\write\@enotes{%
      \@doanenote{\@theenmark}{\@theenvalue}%
   }%
   \begingroup
   \def\next{#1}%
   \newlinechar='40
   \immediate\write\@enotes{\meaning\next}%
   \endgroup
   \immediate\write\@enotes{%
      \@endanenote
   }%
}%
\def\theendnotes{%
\immediate\closeout\@enotes
\global\@enotesopenfalse
\begingroup
\makeatletter
\edef\@tempa{`\string>}%
\ifnum\catcode\@tempa=12
   \let\@ResetGT\relax
\else
   \edef\@ResetGT{\noexpand\catcode\@tempa=\the\catcode\@tempa}%
   \@makeother\>%
\fi
\def\@doanenote##1##2##3>{%
\def\@theenmark{##1}%
\def\@theenvalue{##2}%
\par
%\smallskip %<-small vertical gap between endnotes
\begingroup
%\def\href{\expandafter\savedhref}%
%\def\url{\expandafter\savedurl}%
\@ResetGT
\edef\@currentlabel{\csname p@endnote\endcsname\@theenmark}%
\enoteformat
}%
\def\@endanenote{%
   \par\endgroup
}%
% Redefine, how numbers are formatted in the endnotes-section:
\renewcommand*\@makeenmark{\noindent{\enmarkfont\@theenmark\kern3pt}%4
}%
% header of endnotes-section
\enoteheading
% font-size of endnotes
\enotesize
\input{\jobname.ent}%
\endgroup
}%
\def\enoteformat{%
\rightskip\z@
%\leftskip1.8em
\parindent11\p@
{%
\setcounter{Hendnote}{\@theenvalue}%
\addtocounter{Hendnote}{-1}%
\refstepcounter{Hendnote}%
\ifenotelinks
   \expandafter\@secondoftwo
\else
   \expandafter\@firstoftwo
\fi
{\@firstofone}%
%{\hyperlink{Hendnotepage.\@theenvalue}}%
{\makeenmark}%
}%
}%
% stop redefining portions of endnotes-package:
\makeatother
% Toggle switch in order to turn on/off back-links in the
% endnote-section:
\enotelinkstrue
%\enotelinksfalse
%%%%%%%End note links%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%TOC Macros for Issue%%%%%%%%%%%%%%%
\usepackage{scalefnt}
\def\issdatefont{\fontsize{10}{10}\fontfamily{mns}\selectfont}
\def\issuetocfont{\fontsize{9.5}{10}\fontfamily{mns}\selectfont}
\def\aufont{\fontsize{9.5}{10}\fontfamily{mns}\selectfont}

\sodef\tockern{}{1.4pt}{0pt}{0pt}

\def\issdate#1{\gdef\@issdate{#1}}\issdate{}%

\def\tocenv{\hspace*{140pt}{\issdatefont\@issdate\quad}\par\addvspace{29.5pt}\noindent{\issuetocfont\tockern{CONTENTS}}\par\vskip1.5pt}

\def\endtocenv{}

\newenvironment{toccontent}{\par\hsize360pt}{\par\vskip2pt}
\def\tocpage#1{\issuetocfont\hfill#1\par}
\def\toctitle#1{\issuetocfont\raggedright#1}
\def\tocauthor#1{{\issuetocfont\scalefont{.7}{\uppercase{{\tockern #1}}}}}

\newdimen\tablemove

\def\tbl#1#2#3{%
   \global\setbox\tabcapbox\vbox{#1}%
   \global\setbox\tabbox\hbox{#2}%
   \global\setbox\tabnotebox\vbox{#3}%
   \noindent\vbox{%
      \tablemove\textwidth%
      \advance\tablemove-\wd\tabbox%
      \divide\tablemove2%
      %\hspace*{\tablemove}
      \vbox{%
         \hsize\wd\tabbox%
         #1%
         \tablefont#2%
         #3}}}

\def\@maketablecaption#1#2{
\setbox\tabcapbox\vbox{{\tablecaptionfont\ifunnumtable\else\noindent{\tablecaptionnumfont#1}\fi{\tablecaptionnumfont}\hskip\tablenumcapsep#2\vphantom{y}\par}}
%\ifdim\wd\tabcapbox<\textwidth
\ifdim\ht\tabcapbox<19pt
   %\centerlast
   {\tablecaptionfont\ifunnumtable\else\noindent{\tablecaptionnumfont#1}\fi{\tablecaptionnumfont}\hskip\tablenumcapsep#2\vphantom{y}\vskip.8pt}\global\unnumtablefalse%
\else
   {\tablecaptionfont\ifunnumtable\else\noindent{\tablecaptionnumfont#1}\fi{\tablecaptionnumfont}\hskip\tablenumcapsep#2\vphantom{y}\vskip.8pt}\global\unnumtablefalse%
\fi}

\newenvironment{authgrp}{}{}

\endinput%
