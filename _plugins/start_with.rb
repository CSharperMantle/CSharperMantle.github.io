module Jekyll
  module StartWithFilter
    def start_with(input, prefix)
      input.start_with?(prefix)
    end
  end
end

Liquid::Template.register_filter(Jekyll::StartWithFilter)
