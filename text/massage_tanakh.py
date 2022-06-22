# -*- coding: utf-8 -*-
import xml.sax
import codecs
import sys
import os
import re

tag_re = re.compile(r'<[^>]+>')

punct_re = re.compile(r'[\.,;:\"?!()[]/\-]')

xml_entity_re = re.compile(r'(&quot;)|(&gt;)|(&lt;)|(&amp;)')

token_re = re.compile(r'(\s*)([^\s]*)(\s*)')

surface_re = re.compile(r'([^\w]*)(\w*)([^\w]*)')

whitespace_tokenization_r = r'([\s]*)([^\s]*)([\s]*)'
whitespace_tokenization_re = re.compile(whitespace_tokenization_r)



whitespace_re = re.compile(r'^\s+$')

def usage():
    sys.stderr.write("Usage:\n     python osis2mql.py filename\n")


def getBasename(pathname):
    filename = pathname.split("/")[-1]
    if "." in filename:
        basename = ".".join(filename.split(".")[:-1])
    else:
        basename = filename
    return basename
    

########################################
##
## MQL string mangling
##
########################################
special_re = re.compile(r"[\n\t\"\\]")

special_dict = {
    '\n' : '\\n',
    '\t' : '\\t',
    '"' : '\\"',
    '\\' : '\\\\',
}

upper_bit_re = re.compile(rb'[\x80-\xff]')

def special_sub(mo):
    c = mo.group(0)
    assert len(c) == 1
    return special_dict[c]

def upper_bit_sub(mo):
    c = mo.group(0)
    assert type(c) == type(b"a")
    assert len(c) == 1
    return b"\\x%02x" % ord(c)

def mangleMQLString(ustr):
    result = special_re.sub(special_sub, ustr)
    #print("UP200: ustr = '%s' result = %s, repr(result.encode('utf-8')) = %s, type(result) = %s type(result.encode('utf-8')) = %s" % (ustr, result, repr(result.encode('utf-8')), type(result), type(result.encode('utf-8'))))
    result = upper_bit_re.sub(upper_bit_sub, result.encode('utf-8'))
    result = result.decode('utf-8')
    return result

    
    

def mangle_XML_entities(s):
    r = s.replace("&", "&amp;")
    r = r.replace("<", "&lt;")
    r = r.replace(">", "&gt;")
    r = r.replace("\"", "&quot;")
    return r

class Token:
    def __init__(self, monad, surface, morph, strongs, word_id, word_type, word_n, language, docindex):
        self.monad = monad
        self.surface = surface
        self.morph = morph
        self.strongs = strongs
        if language == "H":
            self.language = "Hebrew"
        elif language == "A":
            self.language = "Aramaic"
        else:
            raise Exception("Unknown token language: %s" % language)
        self.word_id = word_id
        self.word_type = word_type
        self.word_n = word_n
        self.docindex = docindex
        
    def dumpMQL(self, f):
        f.write(("CREATE OBJECT FROM MONADS={%d}\n" % self.monad).encode('utf-8'))
        f.write(("[surface:=\"%s\";\n" % (mangleMQLString(self.surface))).encode('utf-8'))
        f.write(("language:=%s;" % self.language).encode('utf-8'))
        f.write(("docindex:=%d;" % self.docindex).encode('utf-8'))
        f.write(("word_id:=\"%s\";" % self.word_id).encode('utf-8'))
        f.write(("word_type:=\"%s\";" % self.word_type).encode('utf-8'))
        f.write(("word_n:=\"%s\";" % self.word_n).encode('utf-8'))
        f.write(("morph:=\"%s\";" % self.morph).encode('utf-8'))
        f.write(("strongs:=\"%s\";]" % self.strongs).encode('utf-8'))

class NonBibleToken:
    def __init__(self, monad, surface, docindex):
        self.monad = monad
        self.wholesurface = surface
        self.docindex = docindex

    def dumpMQL(self, f):
        f.write(b"CREATE OBJECT FROM MONADS={%d}\n" % self.monad)
        f.write(("[wholesurface:=\"%s\";docindex:=%d;]\n" % (mangleMQLString(self.wholesurface), self.docindex)).encode('utf-8'))

class NonWordBibleToken:
    def __init__(self, monad, surface, docindex):
        self.monad = monad
        self.wholesurface = surface
        self.docindex = docindex

    def dumpMQL(self, f):
        f.write(b"CREATE OBJECT FROM MONADS={%d}\n" % self.monad)
        f.write(("[wholesurface:=\"%s\";docindex:=%d;]\n" % (mangleMQLString(self.wholesurface), self.docindex)).encode('utf-8'))


class SRObject:
    def __init__(self, objectTypeName, starting_monad):
        self.objectTypeName = objectTypeName
        self.fm = starting_monad
        self.lm = starting_monad
        self.stringFeatures = {}
        self.nonStringFeatures = {}
        self.id_d = 0

    def setID_D(self, id_d):
        self.id_d = id_d

    def setStringFeature(self, name, value):
        self.stringFeatures[name] = value

    def setNonStringFeature(self, name, value):
        self.nonStringFeatures[name] = value

    def getStringFeature(self, name):
        return self.stringFeatures[name]

    def setLastMonad(self, ending_monad):
        if ending_monad < self.fm:
            self.lm = self.fm
        else:
            self.lm = ending_monad

    def dumpMQL(self, fout):
        fout.write(("CREATE OBJECT FROM MONADS={%d-%d}" % (self.fm, self.lm)).encode('utf-8'))
        if self.id_d != 0:
            fout.write(("WITH ID_D=%d" % self.id_d).encode('utf-8'))
        fout.write(b"[")
        for key in self.nonStringFeatures:
            value = self.nonStringFeatures[key]
            fout.write(("  %s:=%s;\n" % (key, value)).encode('utf-8'))
        for key in self.stringFeatures:
            value = self.stringFeatures[key]
            fout.write(("  %s:=\"%s\";" % (key, mangleMQLString(value))).encode('utf-8'))
        fout.write(b"]\n")


class TanakhHandler(xml.sax.ContentHandler):
    def __init__(self, bookname):
        self.bookname = bookname
        
        self.elemstack = []
        self.charstack = []

        self.divtypestack = [""] # "" to always have one

        self.bInChapter = False
        self.bInW = False
        self.bInNote = False
        self.bAddToCurrent = False
        self.bAddSpaceToCurrent = False
        self.bInCatchWord = False
        self.bInSeg = False

        self.outlist = []

        self.nixed_elements = set(["teiHeader", "notes", "vs", "cs"])
        self.ignored_elements = set(["tanach", "book"])

        self.nixing_stack = []
        self.single_tag_elements = {
            #"br" : None
        }
        self.handled_elements = set(["names", "name", "abbrev", "number", "filename", "hebrewname", "c", "v", "w"])

        
    def startDocument(self):
        pass

    def endDocument(self):
        pass

    def characters(self, data):
        self.charstack.append(data)

    def getCurElement(self):
        if len(self.elemstack) == 0:
            return ""
        else:
            return self.elemstack[-1]

    def getParentElement(self):
        if len(self.elemstack) < 2:
            return ""
        else:
            return self.elemstack[-2]

    def handleChars(self, chars_before, tag, bIsEndTag):
        if len(self.nixing_stack) > 0:
            bDoIt = False
        else:
            bDoIt = True

        if not bDoIt:
            return

        chars = chars_before

        # Empty strings we do not handle.
        if len(chars) == 0:
            return

        if whitespace_re.match(chars):
            # The whole string consists solely of whitespace.
            # We ignore this string because we have a different way of
            # knowing when to add whitespace.
            #
            # The reason we must have this different way is that the OSHB WLC
            # does not add the whitespace we actually need explicitly.
            #
            # So we have to add this from implicit information.
            #
            pass
        elif not bIsEndTag:
            pass
        else:
            assert bIsEndTag

            if tag == "w":
                self.addWordTokens(chars)
            else:
                assert False, "ERROR: Don't know how to handeChars(chars_before = '%s', tag = '%s', bIsEndTag = %s)." % (chars_before, tag, bIsEndTag)


    def tokenize_on_whitespace(self, chars):
        result_list = []

        for mo in whitespace_tokenization_re.finditer(chars):
            prefix = mo.group(1)
            surface = mo.group(2)
            suffix = mo.group(3)
            result_list.append((prefix, surface, suffix))

        return result_list

    def morph_is_suffix(self, morph):
        return morph[0] == 'S'

    def morph_is_personal_pronoun(self, morph):
        return morph[0:2] == 'Pp'

    def morph_is_preposition(self, morph):
        return morph[0] == 'R'

    def addWordTokens(self, chars):
        pass


    def startElement(self, tag, attributes):
        self.elemstack.append(tag)

        chars = "".join(self.charstack)
        del self.charstack
        self.charstack = []

        self.handleChars(chars, tag, False)

        if tag in self.nixed_elements:
            self.nixing_stack.append(tag)
        elif len(self.nixing_stack) != 0:
            pass
        elif tag in self.simple_SR_elements:
            objectTypeName = self.tag2objectTypeName[tag]
            self.createObject(objectTypeName) 
        elif tag in self.handled_elements:
            self.handleElementStart(tag, attributes)
        elif tag in self.ignored_elements:
            pass
        else:
            raise Exception(("Error: Unknown start-tag '<" + tag + ">'").encode('utf-8'))

    def handleElementStart(self, tag, attributes):
        if tag == "w":
            if "lemma" in attributes:
                lemma = attributes["lemma"]
                #if lemma == "?":
                #    lemma = ""
            else:
                lemma = ""
            arr = [s.strip() for s in lemma.split("/")]
            self.curstrongs = "/".join(arr)

            if "morph" in attributes:
                morph = attributes["morph"]

                # Split off the initial language.
                self.curlanguage = morph[0]

                assert self.curlanguage in set(["H", "A"])
                
                real_tags = morph[1:]
            else:
                real_tags = ""

            self.curmorph = real_tags

            if "id" in attributes:
                self.cur_word_id = attributes["id"]
            else:
                self.cur_word_id = ""

            if "type" in attributes:
                self.cur_word_type = attributes["type"]
                assert self.cur_word_type in set(["x-ketiv"]), "ERROR: Unknown word@type = '%s'" % self.cur_word_type
            else:
                self.cur_word_type = ""

            if "n" in attributes:
                self.cur_word_n = attributes["n"]
            else:
                self.cur_word_n = ""

            self.bInW = True
        elif tag == "seg":
            self.bInSeg = True
            self.seg_type = attributes["type"]

            #print(self.seg_type)
            assert self.seg_type in ["x-sof-pasuq", "x-maqqef", "x-paseq", "x-pe", "x-samekh", "x-large", "x-reversednun", "x-suspended", "x-small"]

            penultimate_tag = self.elemstack[-2]

            if penultimate_tag not in set(["verse"]):
                sys.stderr.write("UP230: <seg type=\"%s\">... occurs with surprising parent tag: <%s>\n" % (self.seg_type, penultimate_tag))
            
            if self.seg_type == "x-maqqef":
                self.bAddToCurrent = True
                self.bAddSpaceToCurrent = False
            elif self.seg_type == "x-sof-pasuq":
                self.bAddToCurrent = True
                self.bAddSpaceToCurrent = True
            elif self.seg_type == "x-pe":
                self.bAddToCurrent = False
                self.bAddSpaceToCurrent = False
            elif self.seg_type == "x-paseq":
                self.bAddToCurrent = False
                self.bAddSpaceToCurrent = False
            elif self.seg_type == "x-samekh":
                self.bAddToCurrent = False
                self.bAddSpaceToCurrent = False
            elif self.seg_type == "x-suspended":
                self.bAddToCurrent = False
                self.bAddSpaceToCurrent = False
            elif self.seg_type == "x-large":
                self.bAddToCurrent = False
                self.bAddSpaceToCurrent = False
            elif self.seg_type == "x-reversednun":
                self.bAddToCurrent = False
                self.bAddSpaceToCurrent = False
            elif self.seg_type == "x-small":
                self.bAddToCurrent = False
                self.bAddSpaceToCurrent = False
            else:
                assert False, "Unknown sef_type: '%s'" % self.seg_type
        elif tag == "v":
            self.endVerse()
            self.startVerse(attributes["v"])
        elif tag == "chapter":
            self.endVerse()
            self.endChapter()
            self.startChapter(attributes["n"])
        elif tag == "title":
            if self.divtypestack[-1] == "bookGroup":
                obj = self.createObject("title")
                obj.setNonStringFeature("divtype", "bookGroup")
            elif self.divtypestack[-1] == "book":
                if self.bInChapter:
                    obj = self.createObject("title")
                    obj.setNonStringFeature("divtype", "chapter")
                else:
                    obj = self.createObject("title")
                    obj.setNonStringFeature("divtype", "book")
        elif tag == "div":
            self.divtypestack.append(attributes["type"])
            if self.divtypestack[-1] == "bookGroup":
                pass
            elif self.divtypestack[-1] == "book":
                self.endVerse()
                self.endChapter()
                self.endBook()
                self.startBook(attributes["osisID"])

    def handleElementEnd(self, tag):
        if tag == "w":
            self.curstrongs = ""
            self.curmorph = ""
            self.cur_word_id = ""
            self.cur_word_type = ""
            self.cur_word_n = ""
            self.bInW = False
            self.bAddToCurrent = False
            self.bAddSpaceToCurrent = False
        elif tag == "seg":
            self.bInSeg = False
            if self.seg_type == "x-maqqef":
                self.bAddToCurrent = True
                self.bAddSpaceToCurrent = False
            elif self.seg_type == "x-sof-pasuq":
                self.bAddToCurrent = False
                self.bAddSpaceToCurrent = False
            elif self.seg_type == "x-pe":
                self.bAddToCurrent = False
                self.bAddSpaceToCurrent = False
                self.endParagraph("pe")
                self.startParagraph()
            elif self.seg_type == "x-samekh":
                self.bAddToCurrent = False
                self.bAddSpaceToCurrent = False
                self.endParagraph("samekh")
                self.startParagraph()
            else:
                self.bAddToCurrent = False
                self.bAddSpaceToCurrent = False
        elif tag == "verse":
            self.endVerse()
        elif tag == "catchWord":
            #self.addNonBibleToken(" (Kethiv) ")
            self.bInCatchWord = False
            objectTypeName = self.tag2objectTypeName[tag]
            self.endObject(objectTypeName)
        elif tag == "rdg":
            #self.addNonBibleToken(" (Qere) ")
            objectTypeName = self.tag2objectTypeName[tag]
            self.endObject(objectTypeName)
        elif tag == "note":
            self.bInNote = False
            if self.note_type == "":
                pass
            elif self.note_type == "variant":
                pass
            else:
                self.endObject("note")
                self.bInNote = False
        elif tag == "chapter":
            pass # All done at start
        elif tag == "title":
            if self.divtypestack[-1] == "bookGroup":
                self.endObject("title")
            elif self.divtypestack[-1] == "book":
                self.endObject("title")
        elif tag == "div":
            self.divtypestack.pop()
            if self.divtypestack[-1] == "bookGroup":
                pass # All done at start
            elif self.divtypestack[-1] == "book":
                pass # All done at start

    def startParagraphIfNotStarted(self):
        if self.paragraph_first_monad < 0:
            self.paragraph_first_monad = self.curmonad
            self.paragraph_docindex = self.curdocindex
            self.curdocindex += 1
 
            
    def startParagraph(self):
        if self.paragraph_first_monad == self.curmonad:
            pass
        else:
            assert self.paragraph_first_monad < 0
            self.paragraph_first_monad = self.curmonad
            self.paragraph_docindex = self.curdocindex
            self.curdocindex += 1

    def endParagraph(self, paragraph_class):
        if self.paragraph_first_monad <= 0:
            return
        elif self.paragraph_first_monad == self.curmonad:
            # Also nothing to do...
            return
        else:
            objectTypeName = "paragraph"
            obj = SRObject(objectTypeName, self.paragraph_first_monad)
            assert self.paragraph_docindex != -1, "ERROR in logic! self.paragraph_docindex == -1. Please fix."
            obj.setNonStringFeature("docindex", self.paragraph_docindex)
            obj.setLastMonad(self.curmonad-1)
            obj.setStringFeature("class", paragraph_class)
            self.objects.setdefault(objectTypeName, []).append(obj)
            self.paragraph_first_monad = -1
            self.paragraph_docindex = -1

    def startBook(self, osisID):
        obj = SRObject("book", self.curmonad)
        obj.setStringFeature("osisID", osisID)
        self.curdocindex = 1
        obj.setNonStringFeature("docindex", self.curdocindex)
        self.curdocindex += 1
        self.curBook = obj

    def endBook(self):
        if self.curBook != None:
            self.curBook.setLastMonad(self.curmonad-1)
            self.objects.setdefault("book", []).append(self.curBook)
            self.curBook = None


    def startChapter(self, osisID):
        self.bInChapter = True
        obj = SRObject("chapter", self.curmonad)
        obj.setStringFeature("osisID", osisID)
        (osisBook, osisChapterStr) = osisID.split(".")
        obj.setStringFeature("osisBook", osisBook)
        obj.setNonStringFeature("chapter", osisChapterStr)
        obj.setNonStringFeature("docindex", self.curdocindex)
        self.curdocindex += 1
        self.curChapter = obj

    def endChapter(self):
        self.bInChapter = False
        if self.curChapter != None:
            self.curChapter.setLastMonad(self.curmonad-1)
            self.objects.setdefault("chapter", []).append(self.curChapter)
            self.curChapter = None


    def startVerse(self, osisID):
        obj = SRObject("verse", self.curmonad)
        obj.setStringFeature("osisID", " %s " % osisID)
        (osisBook, osisChapterStr, osisVerseStr) = osisID.split(".")
        obj.setStringFeature("osisBook", osisBook)
        obj.setNonStringFeature("chapter", osisChapterStr)
        obj.setNonStringFeature("verse", osisVerseStr)
        obj.setNonStringFeature("docindex", self.curdocindex)
        self.curdocindex += 1

        self.curVerse = obj

    def endVerse(self):
        if self.curVerse != None:
            self.curVerse.setLastMonad(self.curmonad-1)
            self.objects.setdefault("verse", []).append(self.curVerse)
            self.curVerse = None

    def endElement(self, tag):
        chars = "".join(self.charstack)
        del self.charstack
        self.charstack = []

        self.handleChars(chars, tag, True)

        self.curmonad -= 1
        self.addCurMonadToObjects()
        self.curmonad += 1


        if tag in self.nixed_elements:
            oldTag = self.nixing_stack.pop()
            assert tag == oldTag
        elif len(self.nixing_stack) != 0:
            if self.nixing_stack[-1] == tag:
                self.nixing_stack.pop()
        elif tag in self.simple_SR_elements:
            objectTypeName = self.tag2objectTypeName[tag]
            self.endObject(objectTypeName)
        elif tag in self.handled_elements:
            self.handleElementEnd(tag)
        elif tag in self.ignored_elements:
            pass
        else:
            raise Exception(("Error: Unknown end-tag " + tag).encode('utf-8'))

        self.elemstack.pop()


    def dumpMQL(self, fout):
        myobject_types = list(sorted(self.objects.keys()))

        for objectTypeName in myobject_types:
            count = 0

            sys.stderr.write("Now dumping [%s] ...\n" % objectTypeName)

            fout.write(b"BEGIN TRANSACTION GO\n")
            fout.write(("CREATE OBJECTS WITH OBJECT TYPE [%s]\n" % objectTypeName).encode('utf-8'))
            for obj in self.objects[objectTypeName]:
                obj.dumpMQL(fout)
                count += 1
                if count == 50000:
                    fout.write(b"GO COMMIT TRANSACTION GO\nBEGIN TRANSACTION GO\n")
                    fout.write(("CREATE OBJECTS WITH OBJECT TYPE [%s]\n" % objectTypeName).encode('utf-8'))
                    count = 0
            fout.write(b"GO\n")
            fout.write(b"COMMIT TRANSACTION GO\n")


        count = 0

        sys.stderr.write("Now dumping [Token] ...\n")

        fout.write(b"BEGIN TRANSACTION GO\n")
        fout.write(b"CREATE OBJECTS WITH OBJECT TYPE [Token]\n")
        for obj in self.tokens:
            obj.dumpMQL(fout)
            count += 1
            if count == 50000:
                fout.write(b"GO COMMIT TRANSACTION GO\nBEGIN TRANSACTION GO\n")
                fout.write(b"CREATE OBJECTS WITH OBJECT TYPE [Token]\n")
                count = 0
        fout.write(b"GO\n")
        fout.write(b"COMMIT TRANSACTION GO\n")

        count = 0
        fout.write(b"BEGIN TRANSACTION GO\n")
        fout.write(b"CREATE OBJECTS WITH OBJECT TYPE [NonBibleToken]\n")
        for obj in self.non_bible_tokens:
            obj.dumpMQL(fout)
            count += 1
            if count == 50000:
                fout.write(b"GO COMMIT TRANSACTION GO\nBEGIN TRANSACTION GO\n")
                fout.write(b"CREATE OBJECTS WITH OBJECT TYPE [NonBibleToken]\n")
                count = 0
        fout.write(b"GO\n")
        fout.write(b"COMMIT TRANSACTION GO\n")

        fout.write(b"VACUUM DATABASE ANALYZE GO\n")

        sys.stderr.write("Finished dumping Book!\n")
        





#booknames_Tanakh = ["Gen","Exod","Lev","Num", "Deut", "Josh", "Judg", "Ruth","1Sam","2Sam", "1Kgs","2Kgs","1Chr", "2Chr","Ezra","Neh","Esth","Job","Ps","Prov","Eccl","Song","Isa", "Jer","Lam","Ezek","Dan","Hos","Joel","Amos","Obad","Jonah","Mic","Nah","Hab","Zeph","Hag","Zech","Mal"]
booknames_Tanakh = ["Genesis"]

booknames_Gen = ["Gen"]

for bookname in booknames_Tanakh:
#for bookname in booknames_Gen: 
    handler = TanakhHandler(bookname)

    infilename = os.path.join('tanach.us', 'Books', '%s.xml' % bookname)
    fin = open(infilename, "rb")

    xml.sax.parse(fin, handler)

    outfilename = os.path.join("massaged_tanakh", "%s.xml" % bookname)
    sys.stderr.write("Now writing: %s ...\n" % outfilename)
    handler.dumpXML(outfilename)
    

fout = open("wlc.mql", "wb")
handler.dumpMQL(fout)
fout.close()

