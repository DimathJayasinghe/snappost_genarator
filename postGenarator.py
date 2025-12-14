import csv
import json
import queue
import re
import threading
import textwrap
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

import requests
from PIL import Image, ImageDraw, ImageFont, ImageOps, ImageTk
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, colorchooser


def _resource_path(value: str) -> str:
	"""Return absolute path for user supplied values."""
	return str(Path(value).expanduser().resolve()) if value else value


class Orientation(Enum):
	LANDSCAPE = "landscape"
	PORTRAIT = "portrait"

	@classmethod
	def from_size(cls, width: int, height: int) -> "Orientation":
		return cls.LANDSCAPE if width >= height else cls.PORTRAIT


@dataclass
class Rectangle:
	x: int
	y: int
	width: int
	height: int

	def as_tuple(self) -> Tuple[int, int, int, int]:
		return self.x, self.y, self.width, self.height

	def to_dict(self) -> Dict[str, int]:
		return {"x": self.x, "y": self.y, "width": self.width, "height": self.height}

	@classmethod
	def from_dict(cls, data: Dict[str, int]) -> "Rectangle":
		return cls(x=int(data["x"]), y=int(data["y"]), width=int(data["width"]), height=int(data["height"]))


@dataclass
class TextStyle:
	font_path: str = ""
	font_size: int = 42
	fill: str = "#000000"
	align: str = "left"
	line_spacing: int = 6

	def to_dict(self) -> Dict[str, object]:
		return {
			"font_path": self.font_path,
			"font_size": self.font_size,
			"fill": self.fill,
			"align": self.align,
			"line_spacing": self.line_spacing,
		}

	@classmethod
	def from_dict(cls, data: Dict[str, object]) -> "TextStyle":
		return cls(
			font_path=data.get("font_path", ""),
			font_size=int(data.get("font_size", 42)),
			fill=data.get("fill", "#000000"),
			align=data.get("align", "left"),
			line_spacing=int(data.get("line_spacing", 6)),
		)


@dataclass
class TextField:
	rect: Rectangle
	style: TextStyle
	prefix: str = ""
	uppercase: bool = False

	def to_dict(self) -> Dict[str, object]:
		return {
			"rect": self.rect.to_dict(),
			"style": self.style.to_dict(),
			"prefix": self.prefix,
			"uppercase": self.uppercase,
		}

	@classmethod
	def from_dict(cls, data: Dict[str, object]) -> "TextField":
		return cls(
			rect=Rectangle.from_dict(data["rect"]),
			style=TextStyle.from_dict(data.get("style", {})),
			prefix=data.get("prefix", ""),
			uppercase=bool(data.get("uppercase", False)),
		)


@dataclass
class TemplateLayout:
	orientation: Orientation
	template_path: str
	photo_area: Rectangle
	clicked_by: TextField
	title: TextField
	description: TextField
	badge: Optional[TextField] = None
	badge_format: str = "{0:02d}"

	def to_dict(self) -> Dict[str, object]:
		return {
			"orientation": self.orientation.value,
			"template_path": self.template_path,
			"photo_area": self.photo_area.to_dict(),
			"clicked_by": self.clicked_by.to_dict(),
			"title": self.title.to_dict(),
			"description": self.description.to_dict(),
			"badge": self.badge.to_dict() if self.badge else None,
			"badge_format": self.badge_format,
		}

	@classmethod
	def from_dict(cls, data: Dict[str, object]) -> "TemplateLayout":
		badge = data.get("badge")
		return cls(
			orientation=Orientation(data["orientation"]),
			template_path=_resource_path(data["template_path"]),
			photo_area=Rectangle.from_dict(data["photo_area"]),
			clicked_by=TextField.from_dict(data["clicked_by"]),
			title=TextField.from_dict(data["title"]),
			description=TextField.from_dict(data["description"]),
			badge=TextField.from_dict(badge) if badge else None,
			badge_format=data.get("badge_format", "{0:02d}"),
		)

	@classmethod
	def empty(cls, orientation: Orientation) -> "TemplateLayout":
		photo_area = Rectangle(0, 0, 100, 100)
		clicked_field = TextField(Rectangle(0, 0, 100, 40), TextStyle())
		title_field = TextField(Rectangle(0, 50, 100, 40), TextStyle())
		description_field = TextField(Rectangle(0, 100, 100, 200), TextStyle())
		return cls(
			orientation=orientation,
			template_path="",
			photo_area=photo_area,
			clicked_by=clicked_field,
			title=title_field,
			description=description_field,
			badge=None,
		)

	def ensure_template_exists(self) -> None:
		if not self.template_path:
			raise ValueError("Template path is not set")
		template_path = Path(self.template_path)
		if not template_path.exists():
			raise FileNotFoundError(f"Template not found: {template_path}")


@dataclass
class ParticipantPhoto:
	sequence: int
	submission_index: int
	participant_name: str
	theme: str
	description: str
	url: str
	local_path: Optional[Path] = None
	orientation: Optional[Orientation] = None

	def filename_slug(self) -> str:
		def _slug(value: str) -> str:
			value = re.sub(r"[^a-zA-Z0-9]+", "-", value.strip()).strip("- ")
			return value.lower()[:60] if value else "item"

		return f"{self.sequence:03d}_{_slug(self.participant_name)}_{_slug(self.theme)}"


class CSVSubmissionRepository:
	"""Parse the response spreadsheet into participant photo entries."""

	REQUIRED_KEYS = {
		"full name": "participant_name",
		"theme name": "theme",
		"description about your photograph": "description",
		"submit your view (photo upload)": "photo_links",
	}

	def __init__(self) -> None:
		self._header_map: Dict[str, str] = {}

	def read_submissions(self, csv_path: Path) -> List[ParticipantPhoto]:
		csv_path = Path(csv_path)
		if not csv_path.exists():
			raise FileNotFoundError(f"CSV file not found: {csv_path}")

		with csv_path.open("r", encoding="utf-8-sig", newline="") as handle:
			reader = csv.DictReader(handle)
			self._prepare_header_map(reader.fieldnames or [])
			sequence = 1
			photos: List[ParticipantPhoto] = []
			for submission_index, row in enumerate(reader, start=1):
				entry = self._map_row(row)
				if not entry:
					continue
				links = self._split_links(entry["photo_links"])
				if not links:
					continue
				for link in links:
					photos.append(
						ParticipantPhoto(
							sequence=sequence,
							submission_index=submission_index,
							participant_name=entry["participant_name"],
							theme=entry["theme"],
							description=entry["description"],
							url=link,
						)
					)
					sequence += 1
		return photos

	def _prepare_header_map(self, headers: Iterable[str]) -> None:
		self._header_map.clear()
		for raw_header in headers:
			key = self._normalize_key(raw_header)
			if key in self.REQUIRED_KEYS:
				self._header_map[self.REQUIRED_KEYS[key]] = raw_header
		missing = [label for label, alias in self.REQUIRED_KEYS.items() if alias not in self._header_map]
		if missing:
			readable = ", ".join(sorted(missing))
			raise ValueError(f"Missing expected columns in CSV: {readable}")

	def _map_row(self, row: Dict[str, str]) -> Optional[Dict[str, str]]:
		mapped: Dict[str, str] = {}
		for alias, header in self._header_map.items():
			mapped[alias] = (row.get(header) or "").strip()
		if not mapped["participant_name"] or not mapped["theme"]:
			return None
		return mapped

	@staticmethod
	def _normalize_key(value: str) -> str:
		return re.sub(r"\s+", " ", value.lower()).strip()

	@staticmethod
	def _split_links(value: str) -> List[str]:
		if not value:
			return []
		chunks = [chunk.strip() for chunk in value.split(",")]
		return [chunk for chunk in chunks if chunk]


class PhotoDownloadError(Exception):
	pass


class ImageDownloadService:
	"""Facade for downloading remote images (Google Drive aware)."""

	DRIVE_HOST = "drive.google.com"

	def __init__(self, session: Optional[requests.Session] = None) -> None:
		self.session = session or requests.Session()

	def download(self, url: str, output_dir: Path) -> Path:
		if not url:
			raise PhotoDownloadError("Empty URL provided")

		output_dir.mkdir(parents=True, exist_ok=True)
		if self.DRIVE_HOST in url:
			return self._download_from_drive(url, output_dir)
		return self._download_generic(url, output_dir)

	def _download_generic(self, url: str, output_dir: Path) -> Path:
		response = self.session.get(url, stream=True, timeout=60)
		if not response.ok:
			raise PhotoDownloadError(f"Unable to download image: {url}")
		filename = self._resolve_filename(url, response.headers.get("Content-Disposition"))
		target = output_dir / filename
		with target.open("wb") as handle:
			for chunk in response.iter_content(1024 * 32):
				handle.write(chunk)
		return target

	def _download_from_drive(self, url: str, output_dir: Path) -> Path:
		file_id = self._extract_drive_id(url)
		if not file_id:
			raise PhotoDownloadError(f"Unable to parse Google Drive id: {url}")
		download_url = "https://drive.google.com/uc?export=download"
		params = {"id": file_id}
		response = self.session.get(download_url, params=params, stream=True)
		token = self._drive_confirm_token(response)
		if token:
			params["confirm"] = token
			response = self.session.get(download_url, params=params, stream=True)
		if not response.ok:
			raise PhotoDownloadError(f"Drive download failed for id {file_id}")
		disposition = response.headers.get("Content-Disposition")
		filename = self._resolve_filename(file_id, disposition)
		target = output_dir / filename
		with target.open("wb") as handle:
			for chunk in response.iter_content(1024 * 32):
				handle.write(chunk)
		return target

	@staticmethod
	def _drive_confirm_token(response: requests.Response) -> Optional[str]:
		for key, value in response.cookies.items():
			if key.startswith("download_warning"):
				return value
		return None

	@staticmethod
	def _resolve_filename(base: str, content_disposition: Optional[str]) -> str:
		if content_disposition:
			match = re.search(r"filename\*=UTF-8''([^;]+)", content_disposition)
			if match:
				return match.group(1)
			match = re.search(r'filename="([^"]+)"', content_disposition)
			if match:
				return match.group(1)
		stem = re.sub(r"[^a-zA-Z0-9_-]+", "", base)
		return f"{stem or 'download'}.jpg"

	@staticmethod
	def _extract_drive_id(url: str) -> Optional[str]:
		patterns = [
			r"id=([a-zA-Z0-9_-]{10,})",
			r"/d/([a-zA-Z0-9_-]{10,})",
			r"file/d/([a-zA-Z0-9_-]{10,})",
		]
		for pattern in patterns:
			match = re.search(pattern, url)
			if match:
				return match.group(1)
		return None


class OrientationDetector:
	"""Detect orientation by inspecting image dimensions."""

	def detect(self, image_path: Path) -> Orientation:
		with Image.open(image_path) as img:
			width, height = img.size
		return Orientation.from_size(width, height)


class FontProvider:
	"""Flyweight provider to reuse font instances."""

	def __init__(self) -> None:
		self._cache: Dict[Tuple[str, int], ImageFont.FreeTypeFont] = {}

	def get(self, style: TextStyle) -> ImageFont.ImageFont:
		key = (style.font_path or "default", style.font_size)
		if key not in self._cache:
			self._cache[key] = self._load(style)
		return self._cache[key]

	@staticmethod
	def _load(style: TextStyle) -> ImageFont.ImageFont:
		font_path = style.font_path or "arial.ttf"
		try:
			return ImageFont.truetype(font_path, style.font_size)
		except OSError:
			return ImageFont.load_default()


class TemplateRenderer:
	"""Strategy that renders participant content on top of template."""

	def __init__(self, font_provider: Optional[FontProvider] = None) -> None:
		self.font_provider = font_provider or FontProvider()

	def render(self, layout: TemplateLayout, photo: ParticipantPhoto) -> Image.Image:
		layout.ensure_template_exists()
		template = Image.open(layout.template_path).convert("RGBA")
		self._paste_photo(template, layout.photo_area, Path(photo.local_path))
		draw = ImageDraw.Draw(template)
		self._draw_text(draw, layout.clicked_by, photo.participant_name)
		self._draw_text(draw, layout.title, photo.theme)
		self._draw_text(draw, layout.description, photo.description)
		if layout.badge and layout.badge_format:
			badge_text = layout.badge_format.format(photo.sequence)
			self._draw_text(draw, layout.badge, badge_text)
		return template.convert("RGB")

	def _paste_photo(self, canvas: Image.Image, area: Rectangle, source_path: Path) -> None:
		if not source_path:
			raise ValueError("No photo path provided")
		with Image.open(source_path).convert("RGB") as source:
			fitted = ImageOps.fit(source, (area.width, area.height), method=Image.Resampling.LANCZOS)
			canvas.paste(fitted, (area.x, area.y))

	def _draw_text(self, draw: ImageDraw.ImageDraw, field: TextField, text: str) -> None:
		font = self.font_provider.get(field.style)
		content = f"{field.prefix}{text or ''}".strip()
		if field.uppercase:
			content = content.upper()
		lines = self._wrap_text(draw, content, font, field.rect.width)
		x, y = field.rect.x, field.rect.y
		for line in lines:
			line_width, line_height = draw.textsize(line, font=font)
			x_position = x
			if field.style.align == "center":
				x_position = x + max((field.rect.width - line_width) // 2, 0)
			elif field.style.align == "right":
				x_position = x + max(field.rect.width - line_width, 0)
			draw.text((x_position, y), line, font=font, fill=field.style.fill)
			y += line_height + field.style.line_spacing
			if y > field.rect.y + field.rect.height:
				break

	@staticmethod
	def _wrap_text(draw: ImageDraw.ImageDraw, text: str, font: ImageFont.ImageFont, max_width: int) -> List[str]:
		if not text:
			return []
		words = text.split()
		if not words:
			return []
		lines: List[str] = []
		current: List[str] = []
		for word in words:
			candidate = " ".join(current + [word]) if current else word
			width, _ = draw.textsize(candidate, font=font)
			if width <= max_width or not current:
				current.append(word)
			else:
				lines.append(" ".join(current))
				current = [word]
		if current:
			lines.append(" ".join(current))
		return lines


class TemplateManager:
	"""Repository that stores template layouts by orientation."""

	def __init__(self) -> None:
		self._layouts: Dict[Orientation, TemplateLayout] = {}
		self._sources: Dict[Orientation, Optional[Path]] = {}

	def set_layout(self, layout: TemplateLayout, source: Optional[Path] = None) -> None:
		self._layouts[layout.orientation] = layout
		self._sources[layout.orientation] = Path(source) if source else None

	def get_layout(self, orientation: Orientation) -> TemplateLayout:
		if orientation not in self._layouts:
			raise ValueError(f"No template configured for {orientation.value}")
		return self._layouts[orientation]

	def get_source_path(self, orientation: Orientation) -> Optional[Path]:
		return self._sources.get(orientation)


class PostGenerationService:
	"""Coordinator that generates posts for the provided submissions."""

	def __init__(
		self,
		template_manager: TemplateManager,
		renderer: TemplateRenderer,
		downloader: ImageDownloadService,
		orientation_detector: OrientationDetector,
	) -> None:
		self.template_manager = template_manager
		self.renderer = renderer
		self.downloader = downloader
		self.orientation_detector = orientation_detector

	def generate(self, photos: Iterable[ParticipantPhoto], output_dir: Path, cache_dir: Path, progress_callback=None) -> List[Path]:
		output_dir = Path(output_dir)
		cache_dir = Path(cache_dir)
		output_dir.mkdir(parents=True, exist_ok=True)
		cache_dir.mkdir(parents=True, exist_ok=True)
		results: List[Path] = []
		for index, photo in enumerate(photos, start=1):
			if progress_callback:
				progress_callback(f"Downloading ({index}): {photo.url}")
			try:
				local = self.downloader.download(photo.url, cache_dir)
			except PhotoDownloadError as err:
				if progress_callback:
					progress_callback(f"Download failed: {err}")
				continue
			photo.local_path = local
			photo.orientation = self.orientation_detector.detect(local)
			try:
				layout = self.template_manager.get_layout(photo.orientation)
			except ValueError as err:
				if progress_callback:
					progress_callback(str(err))
				continue
			if progress_callback:
				progress_callback(f"Rendering ({index}) using {photo.orientation.value} template")
			composed = self.renderer.render(layout, photo)
			filename = f"{photo.filename_slug()}.png"
			output_path = output_dir / filename
			composed.save(output_path, format="PNG")
			results.append(output_path)
			if progress_callback:
				progress_callback(f"Saved {output_path.name}")
		return results


class LogHandler:
	"""Thread-safe logger for the GUI."""

	def __init__(self, widget: tk.Text) -> None:
		self.widget = widget
		self.queue: "queue.Queue[str]" = queue.Queue()
		self.widget.after(100, self._poll)

	def write(self, message: str) -> None:
		self.queue.put(message)

	def _poll(self) -> None:
		try:
			while True:
				message = self.queue.get_nowait()
				self.widget.insert("end", message + "\n")
				self.widget.see("end")
		except queue.Empty:
			pass
		finally:
			self.widget.after(100, self._poll)


class TemplateEditor(tk.Toplevel):
	FIELD_DEFINITIONS: Dict[str, Dict[str, object]] = {
		"photo": {"label": "Photo Area", "has_style": False},
		"badge": {"label": "Badge Number", "has_style": True},
		"clicked_by": {"label": "Clicked By", "has_style": True},
		"title": {"label": "Title", "has_style": True},
		"description": {"label": "Description", "has_style": True},
	}

	def __init__(self, master: tk.Tk, orientation: Orientation, layout: Optional[TemplateLayout], apply_callback) -> None:
		super().__init__(master)
		self.title(f"Template Editor - {orientation.value.title()}")
		self.orientation = orientation
		self.apply_callback = apply_callback
		self.layout = layout or TemplateLayout.empty(orientation)
		self.geometry("1000x720")
		self.resizable(True, True)

		self.canvas = tk.Canvas(self, background="#f0f0f0")
		self.canvas.grid(row=0, column=0, sticky="nsew")

		self.sidebar = ttk.Frame(self)
		self.sidebar.grid(row=0, column=1, sticky="nswe", padx=8, pady=8)

		self.columnconfigure(0, weight=3)
		self.columnconfigure(1, weight=0)
		self.rowconfigure(0, weight=1)

		self._image_tk: Optional[ImageTk.PhotoImage] = None
		self._display_scale: float = 1.0
		self._rect_items: Dict[str, int] = {}
		self._drag_start: Optional[Tuple[int, int]] = None
		self._current_field = tk.StringVar(value="photo")

		self._build_sidebar()
		self._bind_canvas_events()
		if self.layout.template_path:
			self._load_template_image(Path(self.layout.template_path))
		self._draw_existing_rectangles()

	def _build_sidebar(self) -> None:
		ttk.Label(self.sidebar, text="Template Image").pack(anchor="w")
		ttk.Button(self.sidebar, text="Load Template", command=self._choose_template).pack(fill="x", pady=(0, 8))

		ttk.Label(self.sidebar, text="Field").pack(anchor="w")
		for field_key, meta in self.FIELD_DEFINITIONS.items():
			ttk.Radiobutton(
				self.sidebar,
				text=meta["label"],
				value=field_key,
				variable=self._current_field,
				command=self._refresh_field_controls,
			).pack(anchor="w")

		self.controls_container = ttk.Frame(self.sidebar)
		self.controls_container.pack(fill="x", pady=12)

		ttk.Button(self.sidebar, text="Save Config", command=self._save_config).pack(fill="x", pady=(12, 4))
		ttk.Button(self.sidebar, text="Load Config", command=self._load_config).pack(fill="x", pady=(0, 12))
		ttk.Button(self.sidebar, text="Apply to App", command=self._apply_and_close).pack(fill="x")

		self._refresh_field_controls()

	def _bind_canvas_events(self) -> None:
		self.canvas.bind("<ButtonPress-1>", self._on_mouse_press)
		self.canvas.bind("<B1-Motion>", self._on_mouse_drag)
		self.canvas.bind("<ButtonRelease-1>", self._on_mouse_release)

	def _refresh_field_controls(self) -> None:
		for child in self.controls_container.winfo_children():
			child.destroy()
		field_key = self._current_field.get()
		has_style = self.FIELD_DEFINITIONS[field_key]["has_style"]
		ttk.Label(self.controls_container, text="Rectangle").pack(anchor="w")
		ttk.Label(self.controls_container, text="Drag on template to set area").pack(anchor="w")
		if has_style:
			ttk.Separator(self.controls_container).pack(fill="x", pady=4)
			ttk.Label(self.controls_container, text="Text Style").pack(anchor="w")
			layout_field = self._get_field(field_key)
			ttk.Button(self.controls_container, text="Font File", command=lambda: self._choose_font(layout_field)).pack(fill="x", pady=(2, 2))
			ttk.Label(self.controls_container, text=f"Current: {Path(layout_field.style.font_path).name if layout_field.style.font_path else 'Default'}").pack(anchor="w")

			ttk.Label(self.controls_container, text="Font Size").pack(anchor="w")
			size_var = tk.IntVar(value=layout_field.style.font_size)

			def update_size(*_):
				layout_field.style.font_size = max(6, size_var.get())

			size_entry = ttk.Spinbox(self.controls_container, from_=6, to=256, textvariable=size_var, command=update_size)
			size_entry.pack(fill="x")
			size_var.trace_add("write", lambda *_: update_size())

			ttk.Label(self.controls_container, text="Color").pack(anchor="w", pady=(4, 0))
			ttk.Button(self.controls_container, text=layout_field.style.fill, command=lambda: self._choose_color(layout_field)).pack(fill="x")

			ttk.Label(self.controls_container, text="Alignment").pack(anchor="w", pady=(4, 0))
			align_var = tk.StringVar(value=layout_field.style.align)

			def update_align(*_):
				layout_field.style.align = align_var.get()

			ttk.OptionMenu(self.controls_container, align_var, layout_field.style.align, "left", "center", "right", command=lambda *_: update_align()).pack(fill="x")

			ttk.Label(self.controls_container, text="Line Spacing").pack(anchor="w", pady=(4, 0))
			spacing_var = tk.IntVar(value=layout_field.style.line_spacing)

			def update_spacing(*_):
				layout_field.style.line_spacing = spacing_var.get()

			ttk.Spinbox(self.controls_container, from_=0, to=100, textvariable=spacing_var, command=update_spacing).pack(fill="x")
			spacing_var.trace_add("write", lambda *_: update_spacing())

			ttk.Label(self.controls_container, text="Prefix").pack(anchor="w", pady=(4, 0))
			prefix_var = tk.StringVar(value=layout_field.prefix)

			def update_prefix(*_):
				layout_field.prefix = prefix_var.get()

			ttk.Entry(self.controls_container, textvariable=prefix_var).pack(fill="x")
			prefix_var.trace_add("write", lambda *_: update_prefix())

			uppercase_var = tk.BooleanVar(value=layout_field.uppercase)

			def update_uppercase() -> None:
				layout_field.uppercase = uppercase_var.get()

			ttk.Checkbutton(self.controls_container, text="Uppercase", variable=uppercase_var, command=update_uppercase).pack(anchor="w", pady=(4, 0))

			if field_key == "badge":
				ttk.Label(self.controls_container, text="Badge Format e.g. {0:02d}").pack(anchor="w", pady=(8, 0))
				badge_var = tk.StringVar(value=self.layout.badge_format)

				def update_badge(*_):
					self.layout.badge_format = badge_var.get() or "{0:02d}"

				ttk.Entry(self.controls_container, textvariable=badge_var).pack(fill="x")
				badge_var.trace_add("write", lambda *_: update_badge())

	def _get_field(self, key: str) -> TextField:
		if key == "photo":
			return TextField(self.layout.photo_area, TextStyle())
		if key == "badge":
			if not self.layout.badge:
				self.layout.badge = TextField(Rectangle(0, 0, 100, 100), TextStyle(align="center"))
			return self.layout.badge
		if key == "clicked_by":
			return self.layout.clicked_by
		if key == "title":
			return self.layout.title
		return self.layout.description

	def _choose_template(self) -> None:
		path = filedialog.askopenfilename(title="Select Template Image", filetypes=[("Image Files", "*.png;*.jpg;*.jpeg"), ("All Files", "*.*")])
		if not path:
			return
		self.layout.template_path = path
		self._load_template_image(Path(path))

	def _load_template_image(self, path: Path) -> None:
		image = Image.open(path)
		self._image = image
		max_width, max_height = 740, 680
		scale = min(max_width / image.width, max_height / image.height, 1.0)
		self._display_scale = scale
		display = image.resize((int(image.width * scale), int(image.height * scale)))
		self._image_tk = ImageTk.PhotoImage(display)
		self.canvas.delete("all")
		self.canvas.create_image(0, 0, anchor="nw", image=self._image_tk)
		self.canvas.configure(scrollregion=(0, 0, display.width, display.height))
		self._draw_existing_rectangles()

	def _draw_existing_rectangles(self) -> None:
		self.canvas.delete("rect")
		def draw_field(name: str, rect: Rectangle, color: str) -> None:
			if not rect:
				return
			scaled = self._scale_rect(rect)
			self._rect_items[name] = self.canvas.create_rectangle(*scaled, outline=color, width=2, tags="rect")

		draw_field("photo", self.layout.photo_area, "#2f80ed")
		if self.layout.badge:
			draw_field("badge", self.layout.badge.rect, "#9b51e0")
		draw_field("clicked_by", self.layout.clicked_by.rect, "#27ae60")
		draw_field("title", self.layout.title.rect, "#f2994a")
		draw_field("description", self.layout.description.rect, "#eb5757")

	def _scale_rect(self, rect: Rectangle) -> Tuple[int, int, int, int]:
		scale = self._display_scale
		return (
			int(rect.x * scale),
			int(rect.y * scale),
			int((rect.x + rect.width) * scale),
			int((rect.y + rect.height) * scale),
		)

	def _on_mouse_press(self, event) -> None:
		if not hasattr(self, "_image"):
			return
		self._drag_start = (event.x, event.y)

	def _on_mouse_drag(self, event) -> None:
		if not self._drag_start:
			return
		x0, y0 = self._drag_start
		rect = (x0, y0, event.x, event.y)
		field_key = self._current_field.get()
		if field_key not in self._rect_items:
			self._rect_items[field_key] = self.canvas.create_rectangle(*rect, outline="#000", dash=(2, 2), tags="rect")
		else:
			self.canvas.coords(self._rect_items[field_key], *rect)

	def _on_mouse_release(self, event) -> None:
		if not self._drag_start:
			return
		x0, y0 = self._drag_start
		self._drag_start = None
		x1, y1 = event.x, event.y
		rect = self._normalize_rect(x0, y0, x1, y1)
		if not rect:
			return
		image_rect = self._to_image_rect(rect)
		field_key = self._current_field.get()
		if field_key == "photo":
			self.layout.photo_area = image_rect
		elif field_key == "badge":
			if not self.layout.badge:
				self.layout.badge = TextField(image_rect, TextStyle(align="center"))
			else:
				self.layout.badge.rect = image_rect
		elif field_key == "clicked_by":
			self.layout.clicked_by.rect = image_rect
		elif field_key == "title":
			self.layout.title.rect = image_rect
		else:
			self.layout.description.rect = image_rect
		self._draw_existing_rectangles()

	@staticmethod
	def _normalize_rect(x0: int, y0: int, x1: int, y1: int) -> Optional[Tuple[int, int, int, int]]:
		left, right = sorted((x0, x1))
		top, bottom = sorted((y0, y1))
		if abs(right - left) < 5 or abs(bottom - top) < 5:
			return None
		return left, top, right, bottom

	def _to_image_rect(self, rect: Tuple[int, int, int, int]) -> Rectangle:
		scale = 1.0 / self._display_scale
		x0 = int(rect[0] * scale)
		y0 = int(rect[1] * scale)
		x1 = int(rect[2] * scale)
		y1 = int(rect[3] * scale)
		return Rectangle(x=x0, y=y0, width=x1 - x0, height=y1 - y0)

	def _choose_font(self, field: TextField) -> None:
		path = filedialog.askopenfilename(title="Select Font", filetypes=[("Font Files", "*.ttf;*.otf"), ("All Files", "*.*")])
		if path:
			field.style.font_path = path
			self._refresh_field_controls()

	def _choose_color(self, field: TextField) -> None:
		color = colorchooser.askcolor(color=field.style.fill)
		if color and color[1]:
			field.style.fill = color[1]
			self._refresh_field_controls()

	def _save_config(self) -> None:
		if not self.layout.template_path:
			messagebox.showerror("Missing Template", "Load a template image before saving the configuration.")
			return
		initial = None
		if hasattr(self.master, "template_manager"):
			try:
				initial = self.master.template_manager.get_source_path(self.orientation)
			except ValueError:
				initial = None
		path = filedialog.asksaveasfilename(
			title="Save Template Configuration",
			defaultextension=".json",
			filetypes=[("Template Config", "*.json"), ("All Files", "*.*")],
			initialfile=f"{self.orientation.value}_template.json" if not initial else initial.name,
		)
		if not path:
			return
		data = self.layout.to_dict()
		with open(path, "w", encoding="utf-8") as handle:
			json.dump(data, handle, indent=2)
		messagebox.showinfo("Saved", f"Template configuration saved to {path}")

	def _load_config(self) -> None:
		path = filedialog.askopenfilename(title="Load Template Configuration", filetypes=[("Template Config", "*.json"), ("All Files", "*.*")])
		if not path:
			return
		with open(path, "r", encoding="utf-8") as handle:
			data = json.load(handle)
		layout = TemplateLayout.from_dict(data)
		if layout.orientation != self.orientation:
			messagebox.showerror("Orientation Mismatch", "Loaded template orientation does not match the editor mode.")
			return
		self.layout = layout
		self._load_template_image(Path(layout.template_path))
		self._refresh_field_controls()
		messagebox.showinfo("Loaded", "Template configuration loaded.")

	def _apply_and_close(self) -> None:
		if not self.layout.template_path:
			messagebox.showerror("Missing Template", "Load a template image before applying the configuration.")
			return
		if self.apply_callback:
			self.apply_callback(self.layout)
		self.destroy()


class SnapshotApp(tk.Tk):
	def __init__(self) -> None:
		super().__init__()
		self.title("Snapshot Post Generator")
		self.geometry("1024x720")

		self.template_manager = TemplateManager()
		self.repository = CSVSubmissionRepository()
		self.orientation_detector = OrientationDetector()
		self.renderer = TemplateRenderer()
		self.downloader = ImageDownloadService()
		self.generator = PostGenerationService(
			template_manager=self.template_manager,
			renderer=self.renderer,
			downloader=self.downloader,
			orientation_detector=self.orientation_detector,
		)

		self.csv_path_var = tk.StringVar()
		self.output_dir_var = tk.StringVar(value=str(Path.cwd() / "output"))
		self.cache_dir_var = tk.StringVar(value=str(Path.cwd() / "cache"))
		self.status_var = tk.StringVar(value="Idle")

		self._build_ui()

	def _build_ui(self) -> None:
		container = ttk.Frame(self)
		container.pack(fill="both", expand=True, padx=12, pady=12)

		file_frame = ttk.LabelFrame(container, text="Inputs")
		file_frame.pack(fill="x", pady=8)
		self._build_file_inputs(file_frame)

		template_frame = ttk.LabelFrame(container, text="Templates")
		template_frame.pack(fill="x", pady=8)
		self._build_template_controls(template_frame)

		action_frame = ttk.Frame(container)
		action_frame.pack(fill="x", pady=8)
		ttk.Button(action_frame, text="Generate Posts", command=self._start_generation).pack(side="left")
		ttk.Label(action_frame, textvariable=self.status_var).pack(side="left", padx=12)

		log_frame = ttk.LabelFrame(container, text="Activity Log")
		log_frame.pack(fill="both", expand=True)
		self.log_widget = tk.Text(log_frame, height=18, state="normal")
		self.log_widget.pack(fill="both", expand=True)
		self.log_handler = LogHandler(self.log_widget)

	def _build_file_inputs(self, frame: ttk.Frame) -> None:
		ttk.Label(frame, text="Responses CSV").grid(row=0, column=0, sticky="w")
		ttk.Entry(frame, textvariable=self.csv_path_var, width=80).grid(row=0, column=1, sticky="we", padx=6)
		ttk.Button(frame, text="Browse", command=self._choose_csv).grid(row=0, column=2)

		ttk.Label(frame, text="Output Folder").grid(row=1, column=0, sticky="w", pady=4)
		ttk.Entry(frame, textvariable=self.output_dir_var, width=80).grid(row=1, column=1, sticky="we", padx=6)
		ttk.Button(frame, text="Browse", command=lambda: self._choose_directory(self.output_dir_var)).grid(row=1, column=2)

		ttk.Label(frame, text="Download Cache").grid(row=2, column=0, sticky="w", pady=4)
		ttk.Entry(frame, textvariable=self.cache_dir_var, width=80).grid(row=2, column=1, sticky="we", padx=6)
		ttk.Button(frame, text="Browse", command=lambda: self._choose_directory(self.cache_dir_var)).grid(row=2, column=2)

		frame.columnconfigure(1, weight=1)

	def _build_template_controls(self, frame: ttk.Frame) -> None:
		ttk.Label(frame, text="Landscape Template").grid(row=0, column=0, sticky="w")
		ttk.Button(frame, text="Edit", command=lambda: self._open_editor(Orientation.LANDSCAPE)).grid(row=0, column=1, padx=4)
		ttk.Button(frame, text="Load Config", command=lambda: self._load_template_config(Orientation.LANDSCAPE)).grid(row=0, column=2, padx=4)
		self.landscape_status = ttk.Label(frame, text="Not configured", foreground="#b00020")
		self.landscape_status.grid(row=0, column=3, sticky="w")

		ttk.Label(frame, text="Portrait Template").grid(row=1, column=0, sticky="w", pady=(4, 0))
		ttk.Button(frame, text="Edit", command=lambda: self._open_editor(Orientation.PORTRAIT)).grid(row=1, column=1, padx=4)
		ttk.Button(frame, text="Load Config", command=lambda: self._load_template_config(Orientation.PORTRAIT)).grid(row=1, column=2, padx=4)
		self.portrait_status = ttk.Label(frame, text="Not configured", foreground="#b00020")
		self.portrait_status.grid(row=1, column=3, sticky="w")

		for idx in range(4):
			frame.columnconfigure(idx, weight=1 if idx == 3 else 0)

	def _choose_csv(self) -> None:
		path = filedialog.askopenfilename(title="Select Responses CSV", filetypes=[("CSV", "*.csv"), ("All Files", "*.*")])
		if path:
			self.csv_path_var.set(path)

	def _choose_directory(self, variable: tk.StringVar) -> None:
		path = filedialog.askdirectory()
		if path:
			variable.set(path)

	def _open_editor(self, orientation: Orientation) -> None:
		layout = None
		try:
			layout = self.template_manager.get_layout(orientation)
		except ValueError:
			layout = None

		def apply_callback(new_layout: TemplateLayout) -> None:
			self.template_manager.set_layout(new_layout)
			self._update_template_status()
			messagebox.showinfo("Applied", f"{orientation.value.title()} template updated")

		TemplateEditor(self, orientation, layout, apply_callback)

	def _load_template_config(self, orientation: Orientation) -> None:
		path = filedialog.askopenfilename(title="Load Template Config", filetypes=[("Template Config", "*.json"), ("All Files", "*.*")])
		if not path:
			return
		with open(path, "r", encoding="utf-8") as handle:
			data = json.load(handle)
		layout = TemplateLayout.from_dict(data)
		if layout.orientation != orientation:
			messagebox.showerror("Orientation mismatch", "Selected configuration is for a different orientation.")
			return
		self.template_manager.set_layout(layout, source=Path(path))
		self._update_template_status()
		messagebox.showinfo("Loaded", f"{orientation.value.title()} template loaded from {path}")

	def _update_template_status(self) -> None:
		try:
			landscape = self.template_manager.get_layout(Orientation.LANDSCAPE)
			self.landscape_status.configure(text=Path(landscape.template_path).name, foreground="#2e7d32")
		except ValueError:
			self.landscape_status.configure(text="Not configured", foreground="#b00020")
		try:
			portrait = self.template_manager.get_layout(Orientation.PORTRAIT)
			self.portrait_status.configure(text=Path(portrait.template_path).name, foreground="#2e7d32")
		except ValueError:
			self.portrait_status.configure(text="Not configured", foreground="#b00020")

	def _start_generation(self) -> None:
		csv_path = self.csv_path_var.get()
		if not csv_path:
			messagebox.showerror("Missing CSV", "Select the responses CSV file first.")
			return
		try:
			self.template_manager.get_layout(Orientation.LANDSCAPE)
			self.template_manager.get_layout(Orientation.PORTRAIT)
		except ValueError as err:
			messagebox.showerror("Missing Template", str(err))
			return

		output_dir = Path(self.output_dir_var.get())
		cache_dir = Path(self.cache_dir_var.get())
		self.status_var.set("Preparing...")
		self.log_handler.write("Starting generation...")

		def worker() -> None:
			try:
				photos = self.repository.read_submissions(Path(csv_path))
			except Exception as err:
				self._on_generation_finished(f"Failed to parse CSV: {err}")
				return

			if not photos:
				self._on_generation_finished("No photos found in CSV")
				return

			def progress(message: str) -> None:
				self.log_handler.write(message)

			try:
				results = self.generator.generate(photos, output_dir, cache_dir, progress_callback=progress)
			except Exception as err:  # noqa: BLE001
				self._on_generation_finished(f"Generation failed: {err}")
				return
			self._on_generation_finished(f"Done. Generated {len(results)} posts in {output_dir}")

		threading.Thread(target=worker, daemon=True).start()

	def _on_generation_finished(self, message: str) -> None:
		def update() -> None:
			self.status_var.set(message)
			self.log_handler.write(message)

		self.after(0, update)


def main() -> None:
	app = SnapshotApp()
	app.mainloop()


if __name__ == "__main__":
	main()
