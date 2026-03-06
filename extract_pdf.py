import fitz
doc = fitz.open(r'c:\ANUP\MTP\Base Paper\Implemented Scheme.pdf')
for i, page in enumerate(doc):
    text = page.get_text()
    print(f'=== PAGE {i+1} ===')
    print(text)
print(f'\nTotal pages: {len(doc)}')
